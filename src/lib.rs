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

use std::cmp::Ordering;
use std::fmt::Display;
use std::fs::OpenOptions;
use std::os::unix::fs::FileExt;
use std::path::Path;

use anyhow::bail;
use anyhow::Context;

use crate::btree::BtreeContext;
use crate::cursor::BtreeCursor;
use crate::cursor::BtreePayload;
use crate::pager::PageId;
use crate::pager::Pager;
use crate::parser::expect_no_more_token;
use crate::parser::expect_semicolon;
use crate::parser::parse_sql;
use crate::parser::BinaryOp;
use crate::parser::CompareOp;
use crate::parser::Error as ParseError;
use crate::parser::Expr;
use crate::parser::Insert;
use crate::parser::Parser;
use crate::parser::ResultColumn;
use crate::parser::Select;
use crate::parser::Stmt;
use crate::parser::UnaryOp;
use crate::record::build_record;
use crate::record::parse_record;
use crate::record::parse_record_header;
use crate::record::SerialType;
use crate::schema::calc_collation;
use crate::schema::calc_type_affinity;
use crate::schema::ColumnNumber;
use crate::schema::Schema;
use crate::schema::Table;
pub use crate::value::Buffer;
use crate::value::Collation;
use crate::value::TypeAffinity;
pub use crate::value::Value;
use crate::value::ValueCmp;
use crate::value::DEFAULT_COLLATION;

const SQLITE_MAX_PAGE_SIZE: u32 = 65536;
pub const DATABASE_HEADER_SIZE: usize = 100;
const MAGIC_HEADER: &[u8; 16] = b"SQLite format 3\0";
// Original SQLite support both 32-bit or 64-bit rowid. prsqlite only support
// 64-bit rowid.
const MAX_ROWID: i64 = i64::MAX;

#[derive(Debug)]
pub enum Error<'a> {
    Parse(ParseError<'a>),
    Other(anyhow::Error),
}

impl<'a> From<ParseError<'a>> for Error<'a> {
    fn from(e: ParseError<'a>) -> Self {
        Self::Parse(e)
    }
}

impl From<anyhow::Error> for Error<'_> {
    fn from(e: anyhow::Error) -> Self {
        Self::Other(e)
    }
}

impl Display for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Parse(e) => {
                write!(f, "SQL parser error: {}", e)
            }
            Error::Other(e) => write!(f, "{}", e),
        }
    }
}

pub type Result<'a, T> = std::result::Result<T, Error<'a>>;

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
        // TODO: support read only mode.
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(filename)
            .with_context(|| format!("failed to open file: {:?}", filename))?;
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

    pub fn prepare<'a>(&mut self, sql: &'a str) -> Result<'a, Statement> {
        let input = sql.as_bytes();
        let mut parser = Parser::new(input);
        let statement = parse_sql(&mut parser)?;
        expect_semicolon(&mut parser)?;
        expect_no_more_token(&mut parser)?;

        match statement {
            Stmt::Select(select) => Ok(Statement::Query(self.prepare_select(select)?)),
            Stmt::Insert(insert) => Ok(Statement::Execution(self.prepare_insert(insert)?)),
        }
    }

    fn load_schema(&mut self) -> anyhow::Result<()> {
        let schema_table = Schema::schema_table();
        let columns = schema_table
            .get_all_columns()
            .map(Expression::Column)
            .collect::<Vec<_>>();
        self.schema = Some(Schema::generate(
            SelectStatement::new(self, schema_table.root_page_id, columns, None),
            schema_table,
        )?);
        Ok(())
    }

    fn prepare_select<'a>(&mut self, select: Select<'a>) -> Result<'a, SelectStatement> {
        if self.schema.is_none() {
            self.load_schema()?;
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
                    columns.push(Expression::from(expr, Some(table))?);
                }
                ResultColumn::AllOfTable(_table_name) => {
                    todo!("ResultColumn::AllOfTable");
                }
            }
        }

        let filter = select
            .filter
            .map(|expr| Expression::from(expr, Some(table)))
            .transpose()?;

        let index = if let Some(Expression::BinaryOperator {
            operator: BinaryOp::Compare(CompareOp::Eq),
            left,
            right,
        }) = &filter
        {
            if let Expression::Column((column_number, type_affinity, collation)) = left.as_ref() {
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
                                    const_value.as_value().apply_numeric_affinity(),
                                )
                            }
                            TypeAffinity::Text => ConstantValue::copy_from(
                                const_value.as_value().apply_text_affinity(),
                            ),
                            TypeAffinity::Blob => ConstantValue::copy_from(const_value.as_value()),
                        };
                        // TODO: Consider collation of constant value.
                        Some(IndexInfo {
                            page_id: index.root_page_id,
                            keys: vec![(value, collation.clone())],
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
            Ok(SelectStatement::with_index(
                self,
                table_page_id,
                columns,
                filter,
                index,
            ))
        } else {
            Ok(SelectStatement::new(self, table_page_id, columns, filter))
        }
    }

    fn prepare_insert<'a>(&mut self, insert: Insert<'a>) -> Result<'a, InsertStatement> {
        if self.schema.is_none() {
            self.load_schema()?;
        }

        let schema = self.schema.as_ref().unwrap();
        let table_name = insert.table_name.dequote();
        let table = schema.get_table(&table_name).ok_or(anyhow::anyhow!(
            "table not found: {:?}",
            std::str::from_utf8(&table_name).unwrap_or_default()
        ))?;

        let mut columns_idx = Vec::with_capacity(insert.columns.len());
        for column in insert.columns {
            let column_name = column.dequote();
            if let Some((column_idx, _, _)) = table.get_column(&column_name) {
                columns_idx.push(column_idx);
            } else {
                return Err(Error::Other(anyhow::anyhow!(
                    "column not found: {:?}",
                    std::str::from_utf8(&column_name).unwrap_or_default()
                )));
            }
        }

        let mut records = Vec::with_capacity(insert.values.len());
        for column_values in insert.values {
            let mut columns = table
                .columns
                .iter()
                .map(|column| (Expression::Null, column.type_affinity))
                .collect::<Vec<_>>();
            let mut rowid = None;
            if column_values.len() != columns_idx.len() {
                return Err(Error::Other(anyhow::anyhow!(
                    "{} values for {} columns",
                    column_values.len(),
                    columns_idx.len()
                )));
            }
            for (column, expr) in columns_idx.iter().zip(column_values.into_iter()) {
                match column {
                    ColumnNumber::RowId => {
                        rowid = Some(Expression::from(expr, None)?);
                    }
                    ColumnNumber::Column(column_idx) => {
                        columns[*column_idx].0 = Expression::from(expr, None)?;
                    }
                }
            }
            records.push(InsertRecord { rowid, columns })
        }

        let table_page_id = table.root_page_id;
        Ok(InsertStatement {
            conn: self,
            table_page_id,
            records,
        })
    }
}

#[derive(Debug, Clone)]
enum ConstantValue {
    Integer(i64),
    Real(f64),
    Text(Vec<u8>),
    Blob(Vec<u8>),
}

impl ConstantValue {
    fn copy_from(value: Value) -> Self {
        assert!(value != Value::Null);
        match value {
            Value::Null => unreachable!("null value"),
            Value::Integer(i) => Self::Integer(i),
            Value::Real(f) => Self::Real(f),
            Value::Text(buf) => Self::Text(buf.into_vec()),
            Value::Blob(buf) => Self::Blob(buf.into_vec()),
        }
    }

    fn as_value(&self) -> Value {
        match self {
            Self::Integer(i) => Value::Integer(*i),
            Self::Real(f) => Value::Real(*f),
            Self::Text(text) => Value::Text(text.as_slice().into()),
            Self::Blob(blob) => Value::Blob(blob.as_slice().into()),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum CollateOrigin {
    Column,
    Expression,
}

fn filter_expression_collation(
    collation: Option<(&Collation, CollateOrigin)>,
) -> Option<(&Collation, CollateOrigin)> {
    match collation {
        Some((_, CollateOrigin::Expression)) => collation,
        _ => None,
    }
}

#[derive(Debug, Clone)]
enum Expression {
    Column((ColumnNumber, TypeAffinity, Collation)),
    UnaryOperator {
        operator: UnaryOp,
        expr: Box<Expression>,
    },
    Collate {
        expr: Box<Expression>,
        collation: Collation,
    },
    BinaryOperator {
        operator: BinaryOp,
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

type ExecutionResult<'a> = (
    Value<'a>,
    Option<TypeAffinity>,
    Option<(&'a Collation, CollateOrigin)>,
);

impl Expression {
    fn from(expr: Expr, table: Option<&Table>) -> anyhow::Result<Self> {
        match expr {
            Expr::Null => Ok(Self::Null),
            Expr::Integer(i) => Ok(Self::Const(ConstantValue::Integer(i))),
            Expr::Real(f) => Ok(Self::Const(ConstantValue::Real(f))),
            Expr::Text(text) => Ok(Self::Const(ConstantValue::Text(text.dequote()))),
            Expr::Blob(hex) => Ok(Self::Const(ConstantValue::Blob(hex.decode()))),
            Expr::UnaryOperator { operator, expr } => Ok(Self::UnaryOperator {
                operator,
                expr: Box::new(Self::from(*expr, table)?),
            }),
            Expr::Collate {
                expr,
                collation_name,
            } => Ok(Self::Collate {
                expr: Box::new(Self::from(*expr, table)?),
                collation: calc_collation(&collation_name)?,
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
                if let Some(table) = table {
                    let column_name = column_name.dequote();
                    table
                        .get_column(&column_name)
                        .map(Self::Column)
                        .ok_or(anyhow::anyhow!(
                            "column not found: {}",
                            std::str::from_utf8(&column_name).unwrap_or_default()
                        ))
                } else {
                    bail!("no table context is not specified");
                }
            }
            Expr::Cast { expr, type_name } => Ok(Self::Cast {
                expr: Box::new(Self::from(*expr, table)?),
                type_affinity: calc_type_affinity(&type_name),
            }),
        }
    }

    /// Execute the expression and return the result.
    ///
    /// TODO: The row should be a context object.
    fn execute<'a>(&'a self, row: Option<&'a RowData>) -> anyhow::Result<ExecutionResult<'a>> {
        match self {
            Self::Column((idx, affinity, collation)) => {
                if let Some(row) = row {
                    Ok((
                        row.get_column_value(idx)?,
                        Some(*affinity),
                        Some((collation, CollateOrigin::Column)),
                    ))
                } else {
                    bail!("column value is not available");
                }
            }
            Self::UnaryOperator { operator, expr } => {
                let (value, _, collation) = expr.execute(row)?;
                let value = match operator {
                    UnaryOp::BitNot => {
                        if let Some(i) = value.as_integer() {
                            Value::Integer(!i)
                        } else {
                            Value::Null
                        }
                    }
                    UnaryOp::Minus => match value {
                        Value::Null => Value::Null,
                        Value::Integer(i) => Value::Integer(-i),
                        Value::Real(d) => Value::Real(-d),
                        Value::Text(_) | Value::Blob(_) => Value::Integer(0),
                    },
                };
                Ok((value, None, filter_expression_collation(collation)))
            }
            Self::Collate { expr, collation } => {
                let (value, affinity, _) = expr.execute(row)?;
                Ok((
                    value,
                    // Type affinity is preserved.
                    affinity,
                    Some((collation, CollateOrigin::Expression)),
                ))
            }
            Self::BinaryOperator {
                operator,
                left,
                right,
            } => {
                let (mut left_value, left_affinity, left_collation) = left.execute(row)?;
                let (mut right_value, right_affinity, right_collation) = right.execute(row)?;

                // TODO: Confirm whether collation is preserved after NULL.
                match (&left_value, &right_value) {
                    (Value::Null, _) => return Ok((Value::Null, None, None)),
                    (_, Value::Null) => return Ok((Value::Null, None, None)),
                    _ => {}
                }

                let collation = match (left_collation, right_collation) {
                    (None, _) => right_collation,
                    (Some((_, CollateOrigin::Column)), Some((_, CollateOrigin::Expression))) => {
                        right_collation
                    }
                    _ => left_collation,
                };
                let next_collation = filter_expression_collation(collation);

                match operator {
                    BinaryOp::Compare(compare_op) => {
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

                        let cmp = ValueCmp::new(
                            &left_value,
                            collation.map(|(c, _)| c).unwrap_or(&DEFAULT_COLLATION),
                        )
                        .compare(&right_value);

                        let result = match compare_op {
                            CompareOp::Eq => cmp == Ordering::Equal,
                            CompareOp::Ne => cmp != Ordering::Equal,
                            CompareOp::Lt => cmp == Ordering::Less,
                            CompareOp::Le => cmp != Ordering::Greater,
                            CompareOp::Gt => cmp == Ordering::Greater,
                            CompareOp::Ge => cmp != Ordering::Less,
                        };
                        if result {
                            Ok((Value::Integer(1), None, next_collation))
                        } else {
                            Ok((Value::Integer(0), None, next_collation))
                        }
                    }
                    BinaryOp::Concat => {
                        // Both operands are forcibly converted to text before concatination. Both
                        // are not null.
                        let left = left_value.force_text_buffer();
                        let right = right_value.force_text_buffer();
                        let mut buffer = match left {
                            Buffer::Owned(buf) => buf,
                            Buffer::Ref(buf) => {
                                let mut buffer = Vec::with_capacity(buf.len() + right.len());
                                buffer.extend(buf);
                                buffer
                            }
                        };
                        buffer.extend(right.iter());
                        Ok((Value::Text(Buffer::Owned(buffer)), None, next_collation))
                    }
                }
            }
            Self::Cast {
                expr,
                type_affinity,
            } => {
                let (value, _affinity, collation) = expr.execute(row)?;
                Ok((
                    value.force_apply_type_affinity(*type_affinity),
                    Some(*type_affinity),
                    collation,
                ))
            }
            Self::Null => Ok((Value::Null, None, None)),
            Self::Const(value) => Ok((value.as_value(), None, None)),
        }
    }
}

struct IndexInfo {
    page_id: PageId,
    keys: Vec<(ConstantValue, Collation)>,
    n_extra: usize,
}

pub enum Statement<'conn> {
    Query(SelectStatement<'conn>),
    Execution(InsertStatement<'conn>),
}

impl<'conn> Statement<'conn> {
    pub fn query(&'conn mut self) -> anyhow::Result<Rows<'conn>> {
        match self {
            Self::Query(stmt) => stmt.query(),
            Self::Execution(_) => bail!("execute statement not support query"),
        }
    }

    pub fn execute(&'conn mut self) -> anyhow::Result<usize> {
        match self {
            Self::Query(_) => bail!("select statement not support execute"),
            Self::Execution(stmt) => stmt.execute(),
        }
    }
}

// TODO: make Connection non mut and support multiple statements.
pub struct SelectStatement<'conn> {
    conn: &'conn mut Connection,
    table_page_id: PageId,
    columns: Vec<Expression>,
    filter: Option<Expression>,
    rowid: Option<i64>,
    index: Option<IndexInfo>,
}

impl<'conn> SelectStatement<'conn> {
    pub(crate) fn new(
        conn: &'conn mut Connection,
        table_page_id: PageId,
        columns: Vec<Expression>,
        filter: Option<Expression>,
    ) -> Self {
        let rowid = match &filter {
            Some(Expression::BinaryOperator {
                operator: BinaryOp::Compare(CompareOp::Eq),
                left,
                right,
            }) => match (left.as_ref(), right.as_ref()) {
                (
                    Expression::Column((ColumnNumber::RowId, _, _)),
                    Expression::Const(ConstantValue::Integer(value)),
                ) => Some(*value),
                (
                    Expression::Const(ConstantValue::Integer(value)),
                    Expression::Column((ColumnNumber::RowId, _, _)),
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

    pub fn query(&'conn mut self) -> anyhow::Result<Rows<'conn>> {
        // TODO: ReadLock table/schema.
        // TODO: check schema version.
        let mut cursor =
            BtreeCursor::new(self.table_page_id, &self.conn.pager, &self.conn.btree_ctx)?;
        let index_cursor = if let Some(rowid) = self.rowid {
            cursor.table_move_to(rowid)?;
            None
        } else if let Some(index) = &self.index {
            let mut index_cursor =
                BtreeCursor::new(index.page_id, &self.conn.pager, &self.conn.btree_ctx)?;
            // TODO: IndexInfo should hold ValueCmp instead of ConstantValue.
            let tmp_keys = index
                .keys
                .iter()
                .map(|(v, c)| (v.as_value(), c))
                .collect::<Vec<_>>();
            let mut keys = Vec::with_capacity(index.keys.len() + index.n_extra + 1);
            keys.extend(tmp_keys.iter().map(|(v, c)| ValueCmp::new(v, c)));
            // +1 for rowid
            keys.extend(
                (0..index.n_extra + 1).map(|_| ValueCmp::new(&Value::Null, &DEFAULT_COLLATION)),
            );
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
    stmt: &'conn SelectStatement<'conn>,
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
                let n = payload.load(content_offset, &mut tmp_buf)?;
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
                let skip = matches!(
                    filter.execute(Some(&data))?.0,
                    Value::Null | Value::Integer(0)
                );
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
            index_cursor.move_next()?;
        } else {
            self.cursor.move_next()?;
        }
        if let Some(index_cursor) = &mut self.index_cursor {
            let Some(index_payload) = index_cursor.get_index_payload()? else {
                return Ok(false);
            };
            let mut record = parse_record(&index_payload)?;
            // self.stmt.index must be present if self.index_cursor is present.
            assert!(self.stmt.index.is_some());
            let keys = self.stmt.index.as_ref().unwrap().keys.as_slice();
            if record.len() < keys.len() {
                bail!("index payload is too short");
            }
            for (i, (key, collation)) in keys.iter().enumerate() {
                if ValueCmp::new(&key.as_value(), collation).compare(&record.get(i)?)
                    != Ordering::Equal
                {
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
    stmt: &'a SelectStatement<'a>,
    data: RowData<'a>,
}

impl<'a> Row<'a> {
    pub fn parse(&self) -> anyhow::Result<Columns<'_>> {
        let mut columns = Vec::with_capacity(self.stmt.columns.len());
        for expr in self.stmt.columns.iter() {
            let (value, _, _) = expr.execute(Some(&self.data))?;
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

struct InsertRecord {
    rowid: Option<Expression>,
    columns: Vec<(Expression, TypeAffinity)>,
}

pub struct InsertStatement<'conn> {
    conn: &'conn mut Connection,
    table_page_id: PageId,
    records: Vec<InsertRecord>,
}

impl InsertStatement<'_> {
    pub fn execute(&mut self) -> anyhow::Result<usize> {
        // TODO: Lock table/schema.
        let mut cursor =
            BtreeCursor::new(self.table_page_id, &self.conn.pager, &self.conn.btree_ctx)?;
        let mut n = 0;
        for record in self.records.iter() {
            let mut rowid = None;
            if let Some(rowid_expr) = &record.rowid {
                let (rowid_value, _, _) = rowid_expr.execute(None)?;
                match rowid_value.apply_numeric_affinity() {
                    Value::Null => {
                        // NULL then fallback to generate new rowid.
                    }
                    Value::Integer(rowid_value) => {
                        rowid = Some(rowid_value);
                    }
                    _ => bail!("rowid is not integer"),
                }
            }
            let rowid = if let Some(rowid) = rowid {
                rowid
            } else {
                cursor.move_to_last()?;
                let last_rowid = cursor.get_table_key()?.unwrap_or(0);
                // TODO: 32-bit rowid support.
                if last_rowid == MAX_ROWID {
                    todo!("find unused rowid randomly");
                } else {
                    last_rowid + 1
                }
            };

            // Check rowid conflict
            let current_rowid = cursor.table_move_to(rowid)?;
            if current_rowid.is_some() && current_rowid.unwrap() == rowid {
                bail!("the rowid already exists");
            }

            let mut columns = Vec::with_capacity(record.columns.len());
            for (expr, _type_affinity) in record.columns.iter() {
                let (value, _, _) = expr.execute(None)?;
                // TODO: apply affinity
                columns.push(value);
            }

            let record = build_record(&columns);

            cursor.insert(rowid, &record)?;

            // TODO: insert into index if exists.

            n += 1;
        }

        self.conn.pager.commit()?;
        Ok(n)
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
