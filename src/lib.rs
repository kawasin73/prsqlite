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
use pager::PageId;

// TODO: This is to suppress the unused warning.
// pub use crate::btree::*;
use crate::btree::BtreeContext;
use crate::cursor::BtreeCursor;
use crate::cursor::BtreePayload;
use crate::pager::Pager;
use crate::parser::parse_select;
use crate::parser::BinaryOperator;
use crate::parser::Expr;
use crate::parser::ResultColumn;
use crate::record::parse_record_header;
use crate::record::Record;
use crate::record::SerialType;
use crate::schema::ColumnNumber;
use crate::schema::Schema;
use crate::schema::Table;
use crate::token::get_token_no_space;
use crate::token::Token;
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
            let columns = schema_table.all_column_index().collect::<Vec<_>>();
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
        for column in select.columns.iter() {
            match column {
                ResultColumn::All => {
                    for column_idx in table.all_column_index() {
                        columns.push(column_idx);
                    }
                }
                ResultColumn::ColumnName(column_name) => {
                    let column_name = column_name.dequote();
                    let column_idx =
                        table.get_column_index(&column_name).ok_or(anyhow::anyhow!(
                            "column not found: {}",
                            std::str::from_utf8(&column_name).unwrap_or_default()
                        ))?;
                    columns.push(column_idx);
                }
            }
        }

        let selection = select
            .selection
            .map(|expr| Selection::from(expr, table))
            .transpose()?;

        let index = if let Some(Selection::BinaryOperator {
            operator: BinaryOperator::Eq,
            left,
            right,
        }) = &selection
        {
            if let Selection::Column(column_number) = left.as_ref() {
                if let Selection::Integer(key) = right.as_ref() {
                    let mut next_index = table.indexes.as_ref();
                    while let Some(index) = next_index {
                        if index.columns[0] == *column_number {
                            break;
                        }
                        next_index = index.next.as_ref();
                    }
                    next_index.map(|index| (index.root_page_id, vec![*key, i64::MIN]))
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
                selection,
                index,
            ))
        } else {
            Ok(Statement::new(self, table_page_id, columns, selection))
        }
    }
}

enum Selection {
    Column(ColumnNumber),
    BinaryOperator {
        operator: BinaryOperator,
        left: Box<Selection>,
        right: Box<Selection>,
    },
    Integer(i64),
    Real(f64),
    Text(Vec<u8>),
    Blob(Vec<u8>),
}

impl Selection {
    fn from(expr: Expr, table: &Table) -> anyhow::Result<Self> {
        match expr {
            Expr::Integer(i) => Ok(Self::Integer(i)),
            Expr::Real(f) => Ok(Self::Real(f)),
            Expr::Text(text) => Ok(Self::Text(text.dequote())),
            Expr::Blob(hex) => Ok(Self::Blob(hex.decode())),
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
                    .get_column_index(&column_name)
                    .map(Self::Column)
                    .ok_or(anyhow::anyhow!(
                        "column not found: {}",
                        std::str::from_utf8(&column_name).unwrap_or_default()
                    ))
            }
        }
    }

    fn execute<'a>(&'a self, row: &'a RowRef) -> anyhow::Result<Value<'a>> {
        match self {
            Self::Column(idx) => row.get(idx),
            Self::BinaryOperator {
                operator,
                left,
                right,
            } => {
                let left = left.execute(row)?;
                let right = right.execute(row)?;
                let result = if operator == &BinaryOperator::Eq {
                    left == right
                } else if operator == &BinaryOperator::Ne {
                    left != right
                } else {
                    let Value::Integer(left) = left else {
                        bail!("invalid value for selection: {:?}", left);
                    };
                    let Value::Integer(right) = right else {
                        bail!("invalid value for selection: {:?}", left);
                    };
                    match operator {
                        BinaryOperator::Eq => left == right,
                        BinaryOperator::Ne => left != right,
                        BinaryOperator::Lt => left < right,
                        BinaryOperator::Le => left <= right,
                        BinaryOperator::Gt => left > right,
                        BinaryOperator::Ge => left >= right,
                    }
                };
                if result {
                    Ok(Value::Integer(1))
                } else {
                    Ok(Value::Integer(0))
                }
            }
            Self::Integer(value) => Ok(Value::Integer(*value)),
            Self::Real(value) => Ok(Value::Real(*value)),
            Self::Text(value) => Ok(Value::Text(value)),
            Self::Blob(value) => Ok(Value::Blob(value)),
        }
    }
}

// TODO: make Connection non mut and support multiple statements.
pub struct Statement<'conn> {
    conn: &'conn mut Connection,
    table_page_id: PageId,
    columns: Vec<ColumnNumber>,
    selection: Option<Selection>,
    rowid: Option<i64>,
    index: Option<(PageId, Vec<i64>)>,
}

impl<'conn> Statement<'conn> {
    pub(crate) fn new(
        conn: &'conn mut Connection,
        table_page_id: PageId,
        columns: Vec<ColumnNumber>,
        selection: Option<Selection>,
    ) -> Self {
        let rowid = match &selection {
            Some(Selection::BinaryOperator {
                operator: BinaryOperator::Eq,
                left,
                right,
            }) => match (left.as_ref(), right.as_ref()) {
                (Selection::Column(ColumnNumber::RowId), Selection::Integer(value)) => Some(*value),
                (Selection::Integer(value), Selection::Column(ColumnNumber::RowId)) => Some(*value),
                _ => None,
            },
            _ => None,
        };
        Self {
            conn,
            table_page_id,
            columns,
            selection,
            rowid,
            index: None,
        }
    }

    fn with_index(
        conn: &'conn mut Connection,
        table_page_id: PageId,
        columns: Vec<ColumnNumber>,
        selection: Option<Selection>,
        index: Option<(PageId, Vec<i64>)>,
    ) -> Self {
        Self {
            conn,
            table_page_id,
            columns,
            selection,
            rowid: None,
            index,
        }
    }

    pub fn execute(&'conn mut self) -> anyhow::Result<Rows<'conn>> {
        // TODO: check schema version.
        let mut cursor =
            BtreeCursor::new(self.table_page_id, &self.conn.pager, &self.conn.btree_ctx)?;
        let index = if let Some(rowid) = self.rowid {
            cursor.table_move_to(rowid)?;
            None
        } else if let Some((index_page_id, keys)) = &self.index {
            let mut index_cursor =
                BtreeCursor::new(*index_page_id, &self.conn.pager, &self.conn.btree_ctx)?;
            index_cursor.index_move_to(keys)?;
            Some((index_cursor, &keys[..keys.len() - 1]))
        } else {
            cursor.move_to_first()?;
            None
        };
        Ok(Rows {
            stmt: self,
            cursor,
            index,
            is_first_row: true,
            completed: false,
        })
    }
}

pub struct Rows<'conn> {
    stmt: &'conn Statement<'conn>,
    cursor: BtreeCursor<'conn, 'conn>,
    index: Option<(BtreeCursor<'conn, 'conn>, &'conn [i64])>,
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
            use_local_buffer = payload.buf().len() >= (content_offset + content_size) as usize;
            if !use_local_buffer {
                tmp_buf.resize(content_size as usize, 0);
                let n = unsafe { payload.load(content_offset, &mut tmp_buf) }?;
                if n != content_size as usize {
                    bail!("payload does not have enough size");
                }
            };

            if let Some(selection) = &self.stmt.selection {
                let column_value_loader = RowRef {
                    rowid,
                    payload: &payload,
                    tmp_buf: &tmp_buf,
                    headers: &headers,
                    use_local_buffer,
                    content_offset,
                };
                if selection.execute(&column_value_loader)? == Value::Integer(0) {
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
            headers,
            rowid,
            payload,
            content_offset,
            use_local_buffer,
            tmp_buf,
        }))
    }

    fn move_next(&mut self) -> anyhow::Result<bool> {
        if self.is_first_row {
            self.is_first_row = false;
        } else if self.stmt.rowid.is_some() {
            // Only one row is selected.
            return Ok(false);
        } else if let Some((index_cursor, _)) = &mut self.index {
            index_cursor.next()?;
        } else {
            self.cursor.next()?;
        }
        if let Some((index_cursor, keys)) = &mut self.index {
            let Some(index_payload) = index_cursor.get_index_payload()? else {
                return Ok(false);
            };
            let mut record = Record::parse(&index_payload)?;
            if record.len() < keys.len() {
                bail!("index payload is too short");
            }
            for (i, key) in keys.iter().enumerate() {
                if let Value::Integer(v) = record.get(i)? {
                    if v != *key {
                        return Ok(false);
                    }
                } else {
                    // TODO: support other key types.
                    bail!("index payload is not integer");
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

fn get_column_value<'a>(
    column_idx: &ColumnNumber,
    rowid: i64,
    payload: &'a BtreePayload<'a, 'a>,
    tmp_buf: &'a [u8],
    headers: &'a [(SerialType, i32)],
    use_local_buffer: bool,
    content_offset: i32,
) -> anyhow::Result<Value<'a>> {
    match column_idx {
        ColumnNumber::Column(idx) => {
            if let Some((serial_type, offset)) = headers.get(*idx) {
                let contents_buffer = if use_local_buffer {
                    &payload.buf()[content_offset as usize..]
                } else {
                    tmp_buf
                };
                serial_type
                    .parse(&contents_buffer[(offset - content_offset) as usize..])
                    .context("parse value")
            } else {
                Ok(STATIC_NULL_VALUE)
            }
        }
        ColumnNumber::RowId => Ok(Value::Integer(rowid)),
    }
}

struct RowRef<'a> {
    rowid: i64,
    payload: &'a BtreePayload<'a, 'a>,
    tmp_buf: &'a [u8],
    headers: &'a [(SerialType, i32)],
    use_local_buffer: bool,
    content_offset: i32,
}

impl<'a> RowRef<'a> {
    fn get(&self, column_idx: &ColumnNumber) -> anyhow::Result<Value> {
        get_column_value(
            column_idx,
            self.rowid,
            self.payload,
            self.tmp_buf,
            self.headers,
            self.use_local_buffer,
            self.content_offset,
        )
    }
}

pub struct Row<'a> {
    stmt: &'a Statement<'a>,
    rowid: i64,
    pub payload: BtreePayload<'a, 'a>,
    headers: Vec<(SerialType, i32)>,
    content_offset: i32,
    use_local_buffer: bool,
    tmp_buf: Vec<u8>,
}

impl<'a> Row<'a> {
    pub fn parse(&self) -> anyhow::Result<Columns<'_>> {
        let mut columns = Vec::with_capacity(self.stmt.columns.len());
        for column_idx in self.stmt.columns.iter() {
            columns.push(get_column_value(
                column_idx,
                self.rowid,
                &self.payload,
                &self.tmp_buf,
                &self.headers,
                self.use_local_buffer,
                self.content_offset,
            )?);
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
