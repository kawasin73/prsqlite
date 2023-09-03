// Copyright 2023 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

mod btree;
mod cursor;
mod pager;
mod parser;
mod record;
mod schema;
#[cfg(test)]
pub mod test_utils;
mod token;
mod utils;
mod value;

use std::fs::File;
use std::os::unix::fs::FileExt;
use std::path::Path;

use anyhow::bail;
use anyhow::Context;

use crate::btree::BtreeContext;
use crate::cursor::BtreeCursor;
use crate::cursor::BtreePayload;
use crate::pager::PageId;
use crate::pager::Pager;
use crate::parser::parse_select;
use crate::parser::BinaryOperator;
use crate::parser::Expr;
use crate::parser::ResultColumn;
use crate::record::parse_record_header;
use crate::record::Record;
use crate::record::SerialType;
use crate::schema::calc_type_affinity;
use crate::schema::ColumnNumber;
use crate::schema::Schema;
use crate::schema::Table;
use crate::token::get_token_no_space;
use crate::token::Token;
use crate::value::TypeAffinity;
pub use crate::value::Value;

const SQLITE_MAX_PAGE_SIZE: u32 = 65536;
pub const DATABASE_HEADER_SIZE: usize = 100;
const MAGIC_HEADER: &[u8; 16] = b"SQLite format 3\0";

pub struct DatabaseHeader<'a>(&'a [u8; DATABASE_HEADER_SIZE]);

impl<'a> DatabaseHeader<'a> {
    pub fn from(buf: &'a [u8; DATABASE_HEADER_SIZE]) -> Self {
        Self(buf)
    }

    pub fn validate_magic_header(&self) -> bool {
        let magic_header: &[u8; 16] = self.0[0..16].try_into().unwrap();
        magic_header == MAGIC_HEADER
    }

    pub fn validate_pagesize(&self) -> bool {
        let pagesize = self.pagesize();
        (512..=SQLITE_MAX_PAGE_SIZE).contains(&pagesize) && (pagesize - 1) & pagesize == 0
    }

    pub fn validate_reserved(&self) -> bool {
        self.pagesize() > self.reserved() as u32
    }

    pub fn pagesize(&self) -> u32 {
        // If the original big endian value is 1, it means 65536.
        (self.0[16] as u32) << 8 | (self.0[17] as u32) << 16
    }

    pub fn reserved(&self) -> u8 {
        self.0[20]
    }

    pub fn usable_size(&self) -> i32 {
        self.pagesize() as i32 - self.reserved() as i32
    }
}

pub struct Connection {
    pager: Pager,
    btree_ctx: BtreeContext,
    schema: Option<Schema>,
}

impl Connection {
    pub fn open(filename: &Path) -> anyhow::Result<Self> {
        let file = File::open(filename)?;
        let mut buf = [0; DATABASE_HEADER_SIZE];
        file.read_exact_at(&mut buf, 0)?;
        let header = DatabaseHeader::from(&buf);
        if !header.validate_magic_header() {
            bail!("invalid magic header");
        } else if !header.validate_pagesize() {
            bail!("invalid pagesize");
        } else if !header.validate_reserved() {
            bail!("invalid reserved");
        }
        let pager = Pager::new(file, header.pagesize() as usize)?;
        Ok(Self {
            pager,
            btree_ctx: BtreeContext::new(header.usable_size()),
            schema: None,
        })
    }

    pub fn prepare(&mut self, sql: &str) -> anyhow::Result<Statement> {
        let input = sql.as_bytes();
        let (n, select) =
            parse_select(input).map_err(|e| anyhow::anyhow!("parse select: {}", e))?;
        let Some((nn, Token::Semicolon)) = get_token_no_space(&input[n..]) else {
            bail!("no semicolon");
        };
        if nn + n != input.len() {
            bail!("extra characters after semicolon");
        }

        if self.schema.is_none() {
            let schema_table = Schema::schema_table();
            let columns = schema_table
                .get_all_columns()
                .map(Expression::Column)
                .collect::<Vec<_>>();
            self.schema = Some(Schema::generate(
                Statement::new(self, schema_table.root_page_id, columns, None),
                schema_table,
            )?);
        }
        let schema = self.schema.as_ref().unwrap();
        let table_name = select.table_name.dequote();
        let table = schema.get_table(&table_name).ok_or(anyhow::anyhow!(
            "table not found: {:?}",
            std::str::from_utf8(&table_name).unwrap_or_default()
        ))?;

        let mut columns = Vec::new();
        for column in select.columns {
            match column {
                ResultColumn::All => {
                    columns.extend(table.get_all_columns().map(Expression::Column));
                }
                ResultColumn::Expr((expr, _alias)) => {
                    // TODO: consider alias.
                    columns.push(Expression::from(expr, table)?);
                }
                ResultColumn::AllOfTable(_table_name) => {
                    todo!("ResultColumn::AllOfTable");
                }
            }
        }

        let filter = select
            .filter
            .map(|expr| Expression::from(expr, table))
            .transpose()?;

        let index = if let Some(Expression::BinaryOperator {
            operator: BinaryOperator::Eq,
            left,
            right,
        }) = &filter
        {
            if let Expression::Column((column_number, type_affinity)) = left.as_ref() {
                if let Expression::Const(const_value) = right.as_ref() {
                    let mut next_index = table.indexes.as_ref();
                    while let Some(index) = next_index {
                        if index.columns[0] == *column_number {
                            break;
                        }
                        next_index = index.next.as_ref();
                    }
                    if let Some(index) = next_index {
                        let value = match type_affinity {
                            TypeAffinity::Integer | TypeAffinity::Real | TypeAffinity::Numeric => {
                                ConstantValue::copy_from(
                                    const_value.as_ref().apply_numeric_affinity(),
                                )
                            }
                            TypeAffinity::Text => {
                                ConstantValue::copy_from(const_value.as_ref().apply_text_affinity())
                            }
                            TypeAffinity::Blob => ConstantValue::copy_from(const_value.as_ref()),
                        };
                        Some(IndexInfo {
                            page_id: index.root_page_id,
                            keys: vec![value],
                            n_extra: index.columns.len() - 1,
                        })
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        };

        let table_page_id = table.root_page_id;
        if index.is_some() {
            Ok(Statement::with_index(
                self,
                table_page_id,
                columns,
                filter,
                index,
            ))
        } else {
            Ok(Statement::new(self, table_page_id, columns, filter))
        }
    }
}

enum ConstantValue {
    Integer(i64),
    Real(f64),
    Text(Vec<u8>),
    Blob(Vec<u8>),
}

impl ConstantValue {
    fn copy_from(value: Value) -> Self {
        assert_ne!(value, Value::Null);
        match value {
            Value::Null => unreachable!("null value"),
            Value::Integer(i) => Self::Integer(i),
            Value::Real(f) => Self::Real(f),
            Value::Text(buf) => Self::Text(buf.into_vec()),
            Value::Blob(buf) => Self::Blob(buf.into_vec()),
        }
    }

    fn as_ref(&self) -> Value {
        match self {
            Self::Integer(i) => Value::Integer(*i),
            Self::Real(f) => Value::Real(*f),
            Self::Text(text) => Value::Text(text.as_slice().into()),
            Self::Blob(blob) => Value::Blob(blob.as_slice().into()),
        }
    }
}

enum Expression {
    Column((ColumnNumber, TypeAffinity)),
    UnaryMinus {
        expr: Box<Expression>,
    },
    BinaryOperator {
        operator: BinaryOperator,
        left: Box<Expression>,
        right: Box<Expression>,
    },
    Cast {
        expr: Box<Expression>,
        type_affinity: TypeAffinity,
    },
    Null,
    Const(ConstantValue),
}

impl Expression {
    fn from(expr: Expr, table: &Table) -> anyhow::Result<Self> {
        match expr {
            Expr::Null => Ok(Self::Null),
            Expr::Integer(i) => Ok(Self::Const(ConstantValue::Integer(i))),
            Expr::Real(f) => Ok(Self::Const(ConstantValue::Real(f))),
            Expr::Text(text) => Ok(Self::Const(ConstantValue::Text(text.dequote()))),
            Expr::Blob(hex) => Ok(Self::Const(ConstantValue::Blob(hex.decode()))),
            Expr::UnaryMinus(expr) => Ok(Self::UnaryMinus {
                expr: Box::new(Self::from(*expr, table)?),
            }),
            Expr::BinaryOperator {
                operator,
                left,
                right,
            } => Ok(Self::BinaryOperator {
                operator,
                left: Box::new(Self::from(*left, table)?),
                right: Box::new(Self::from(*right, table)?),
            }),
            Expr::Column(column_name) => {
                let column_name = column_name.dequote();
                table
                    .get_column(&column_name)
                    .map(Self::Column)
                    .ok_or(anyhow::anyhow!(
                        "column not found: {}",
                        std::str::from_utf8(&column_name).unwrap_or_default()
                    ))
            }
            Expr::Cast { expr, type_name } => Ok(Self::Cast {
                expr: Box::new(Self::from(*expr, table)?),
                type_affinity: calc_type_affinity(&type_name),
            }),
        }
    }

    fn execute<'a>(
        &'a self,
        row: &'a RowData,
    ) -> anyhow::Result<(Value<'a>, Option<TypeAffinity>)> {
        match self {
            Self::Column((idx, affinity)) => Ok((row.get_column_value(idx)?, Some(*affinity))),
            Self::UnaryMinus { expr } => {
                let (value, _) = expr.execute(row)?;
                let value = match value {
                    Value::Null => Value::Null,
                    Value::Integer(i) => Value::Integer(-i),
                    Value::Real(d) => Value::Real(-d),
                    Value::Text(_) | Value::Blob(_) => Value::Integer(0),
                };
                Ok((value, None))
            }
            Self::BinaryOperator {
                operator,
                left,
                right,
            } => {
                let (mut left_value, left_affinity) = left.execute(row)?;
                let (mut right_value, right_affinity) = right.execute(row)?;

                match (&left_value, &right_value) {
                    (Value::Null, _) => return Ok((Value::Null, None)),
                    (_, Value::Null) => return Ok((Value::Null, None)),
                    _ => {}
                }

                // Type Conversions Prior To Comparison
                match (left_affinity, right_affinity) {
                    (
                        Some(TypeAffinity::Integer)
                        | Some(TypeAffinity::Real)
                        | Some(TypeAffinity::Numeric),
                        Some(TypeAffinity::Text) | Some(TypeAffinity::Blob) | None,
                    ) => {
                        right_value = right_value.apply_numeric_affinity();
                    }
                    (
                        Some(TypeAffinity::Text) | Some(TypeAffinity::Blob) | None,
                        Some(TypeAffinity::Integer)
                        | Some(TypeAffinity::Real)
                        | Some(TypeAffinity::Numeric),
                    ) => {
                        left_value = left_value.apply_numeric_affinity();
                    }
                    (Some(TypeAffinity::Text), None) => {
                        right_value = right_value.apply_text_affinity();
                    }
                    (None, Some(TypeAffinity::Text)) => {
                        left_value = left_value.apply_text_affinity();
                    }
                    _ => {}
                }

                let result = match operator {
                    BinaryOperator::Eq => left_value == right_value,
                    BinaryOperator::Ne => left_value != right_value,
                    BinaryOperator::Lt => left_value < right_value,
                    BinaryOperator::Le => left_value <= right_value,
                    BinaryOperator::Gt => left_value > right_value,
                    BinaryOperator::Ge => left_value >= right_value,
                };
                if result {
                    Ok((Value::Integer(1), None))
                } else {
                    Ok((Value::Integer(0), None))
                }
            }
            Self::Cast {
                expr,
                type_affinity,
            } => {
                let (value, _affinity) = expr.execute(row)?;
                Ok((
                    value.force_apply_type_affinity(*type_affinity),
                    Some(*type_affinity),
                ))
            }
            Self::Null => Ok((Value::Null, None)),
            Self::Const(value) => Ok((value.as_ref(), None)),
        }
    }
}

struct IndexInfo {
    page_id: PageId,
    keys: Vec<ConstantValue>,
    n_extra: usize,
}

// TODO: make Connection non mut and support multiple statements.
pub struct Statement<'conn> {
    conn: &'conn mut Connection,
    table_page_id: PageId,
    columns: Vec<Expression>,
    filter: Option<Expression>,
    rowid: Option<i64>,
    index: Option<IndexInfo>,
}

impl<'conn> Statement<'conn> {
    pub(crate) fn new(
        conn: &'conn mut Connection,
        table_page_id: PageId,
        columns: Vec<Expression>,
        filter: Option<Expression>,
    ) -> Self {
        let rowid = match &filter {
            Some(Expression::BinaryOperator {
                operator: BinaryOperator::Eq,
                left,
                right,
            }) => match (left.as_ref(), right.as_ref()) {
                (
                    Expression::Column((ColumnNumber::RowId, _)),
                    Expression::Const(ConstantValue::Integer(value)),
                ) => Some(*value),
                (
                    Expression::Const(ConstantValue::Integer(value)),
                    Expression::Column((ColumnNumber::RowId, _)),
                ) => Some(*value),
                _ => None,
            },
            _ => None,
        };
        Self {
            conn,
            table_page_id,
            columns,
            filter,
            rowid,
            index: None,
        }
    }

    fn with_index(
        conn: &'conn mut Connection,
        table_page_id: PageId,
        columns: Vec<Expression>,
        filter: Option<Expression>,
        index: Option<IndexInfo>,
    ) -> Self {
        Self {
            conn,
            table_page_id,
            columns,
            filter,
            rowid: None,
            index,
        }
    }

    pub fn execute(&'conn mut self) -> anyhow::Result<Rows<'conn>> {
        // TODO: check schema version.
        let mut cursor =
            BtreeCursor::new(self.table_page_id, &self.conn.pager, &self.conn.btree_ctx)?;
        let index_cursor = if let Some(rowid) = self.rowid {
            cursor.table_move_to(rowid)?;
            None
        } else if let Some(index) = &self.index {
            let mut index_cursor =
                BtreeCursor::new(index.page_id, &self.conn.pager, &self.conn.btree_ctx)?;
            let mut keys = Vec::with_capacity(index.keys.len() + index.n_extra + 1);
            keys.extend(index.keys.iter().map(|v| v.as_ref()));
            // +1 for rowid
            keys.extend((0..index.n_extra + 1).map(|_| Value::Null));
            index_cursor.index_move_to(&keys)?;
            Some(index_cursor)
        } else {
            cursor.move_to_first()?;
            None
        };
        Ok(Rows {
            stmt: self,
            cursor,
            index_cursor,
            is_first_row: true,
            completed: false,
        })
    }
}

pub struct Rows<'conn> {
    stmt: &'conn Statement<'conn>,
    cursor: BtreeCursor<'conn, 'conn>,
    index_cursor: Option<BtreeCursor<'conn, 'conn>>,
    is_first_row: bool,
    completed: bool,
}

impl<'conn> Rows<'conn> {
    pub fn next_row(&mut self) -> anyhow::Result<Option<Row<'_>>> {
        if self.completed {
            return Ok(None);
        }

        let mut headers;
        let mut content_offset;
        let mut tmp_buf = Vec::new();
        let mut use_local_buffer;
        loop {
            match self.move_next() {
                Ok(true) => {}
                Ok(false) => {
                    self.completed = true;
                    return Ok(None);
                }
                Err(e) => {
                    self.completed = true;
                    return Err(e);
                }
            }

            let Some((rowid, payload)) = self.cursor.get_table_payload()? else {
                return Ok(None);
            };

            headers = parse_record_header(&payload)?;

            if headers.is_empty() {
                bail!("empty header payload");
            }

            content_offset = headers[0].1;
            let last_header = &headers[headers.len() - 1];
            let content_size = last_header.1 + last_header.0.content_size() - content_offset;
            assert!(content_offset + content_size <= payload.size());
            use_local_buffer = payload.buf().len() >= (content_offset + content_size) as usize;
            if !use_local_buffer {
                tmp_buf.resize(content_size as usize, 0);
                let n = unsafe { payload.load(content_offset, &mut tmp_buf) }?;
                if n != content_size as usize {
                    bail!("payload does not have enough size");
                }
            };

            if let Some(filter) = &self.stmt.filter {
                let data = RowData {
                    rowid,
                    payload,
                    tmp_buf,
                    headers,
                    use_local_buffer,
                    content_offset,
                };
                let skip = matches!(filter.execute(&data)?.0, Value::Null | Value::Integer(0));
                RowData {
                    rowid: _,
                    payload: _,
                    tmp_buf,
                    headers,
                    use_local_buffer,
                    content_offset,
                } = data;
                if skip {
                    continue;
                }
            }

            break;
        }

        let Some((rowid, payload)) = self.cursor.get_table_payload()? else {
            self.completed = true;
            return Ok(None);
        };

        Ok(Some(Row {
            stmt: self.stmt,
            data: RowData {
                headers,
                rowid,
                payload,
                content_offset,
                use_local_buffer,
                tmp_buf,
            },
        }))
    }

    fn move_next(&mut self) -> anyhow::Result<bool> {
        if self.is_first_row {
            self.is_first_row = false;
        } else if self.stmt.rowid.is_some() {
            // Only one row is selected.
            return Ok(false);
        } else if let Some(index_cursor) = &mut self.index_cursor {
            index_cursor.next()?;
        } else {
            self.cursor.next()?;
        }
        if let Some(index_cursor) = &mut self.index_cursor {
            let Some(index_payload) = index_cursor.get_index_payload()? else {
                return Ok(false);
            };
            let mut record = Record::parse(&index_payload)?;
            // self.stmt.index must be present if self.index_cursor is present.
            assert!(self.stmt.index.is_some());
            let keys = self.stmt.index.as_ref().unwrap().keys.as_slice();
            if record.len() < keys.len() {
                bail!("index payload is too short");
            }
            for (i, key) in keys.iter().enumerate() {
                if record.get(i)? != key.as_ref() {
                    return Ok(false);
                }
            }
            let Value::Integer(rowid) = record.get(record.len() - 1)? else {
                bail!("rowid in index is not integer");
            };
            self.cursor.table_move_to(rowid)?;
        }
        Ok(true)
    }
}

const STATIC_NULL_VALUE: Value = Value::Null;

struct RowData<'a> {
    rowid: i64,
    payload: BtreePayload<'a, 'a>,
    headers: Vec<(SerialType, i32)>,
    content_offset: i32,
    use_local_buffer: bool,
    tmp_buf: Vec<u8>,
}

impl<'a> RowData<'a> {
    fn get_column_value(&self, column_idx: &ColumnNumber) -> anyhow::Result<Value> {
        match column_idx {
            ColumnNumber::Column(idx) => {
                if let Some((serial_type, offset)) = self.headers.get(*idx) {
                    let contents_buffer = if self.use_local_buffer {
                        &self.payload.buf()[self.content_offset as usize..]
                    } else {
                        &self.tmp_buf
                    };
                    serial_type
                        .parse(&contents_buffer[(offset - self.content_offset) as usize..])
                        .context("parse value")
                } else {
                    Ok(STATIC_NULL_VALUE)
                }
            }
            ColumnNumber::RowId => Ok(Value::Integer(self.rowid)),
        }
    }
}

pub struct Row<'a> {
    stmt: &'a Statement<'a>,
    data: RowData<'a>,
}

impl<'a> Row<'a> {
    pub fn parse(&self) -> anyhow::Result<Columns<'_>> {
        let mut columns = Vec::with_capacity(self.stmt.columns.len());
        for expr in self.stmt.columns.iter() {
            let (value, _) = expr.execute(&self.data)?;
            columns.push(value);
        }
        Ok(Columns(columns))
    }
}

pub struct Columns<'a>(Vec<Value<'a>>);

impl<'a> Columns<'a> {
    pub fn get(&self, i: usize) -> &Value<'a> {
        self.0.get(i).unwrap_or(&STATIC_NULL_VALUE)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &Value<'a>> {
        self.0.iter()
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;
    use crate::test_utils::*;

    #[test]
    fn pagesize() {
        for shift in 9..16 {
            // 512 ~ 32768
            let size: u16 = 1 << shift;
            let bytes = size.to_be_bytes();
            let mut buf = [0_u8; DATABASE_HEADER_SIZE];
            buf[16] = bytes[0];
            buf[17] = bytes[1];
            let header = DatabaseHeader::from(&buf);

            assert_eq!(header.pagesize(), size as u32);
        }

        // the pagesize "1" means 65536
        let bytes = 1_u16.to_be_bytes();
        let mut buf = [0_u8; DATABASE_HEADER_SIZE];
        buf[16] = bytes[0];
        buf[17] = bytes[1];
        let header = DatabaseHeader::from(&buf);

        assert_eq!(header.pagesize(), 65536);
    }

    #[test]
    fn validate_database_header() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let buf = fs::read(file.path()).unwrap();

        let header = DatabaseHeader::from(buf[0..DATABASE_HEADER_SIZE].try_into().unwrap());

        assert!(header.validate_magic_header());
        assert_eq!(header.pagesize(), 4096);
        assert!(header.validate_pagesize());
        assert!(header.validate_reserved());
    }
}
