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
mod expression;
mod header;
mod pager;
mod parser;
mod payload;
mod query;
mod record;
mod schema;
#[cfg(test)]
pub mod test_utils;
mod token;
mod utils;
mod value;

use std::cell::Cell;
use std::cell::RefCell;
use std::fmt::Display;
use std::fs::OpenOptions;
use std::os::unix::fs::FileExt;
use std::path::Path;

use anyhow::bail;
use anyhow::Context;
use btree::BtreeContext;
use cursor::BtreeCursor;
use expression::Expression;
use header::DatabaseHeader;
use header::DatabaseHeaderMut;
use header::DATABASE_HEADER_SIZE;
use pager::PageId;
use pager::Pager;
use pager::PAGE_ID_1;
use parser::expect_no_more_token;
use parser::expect_semicolon;
use parser::parse_sql;
use parser::Delete;
use parser::Insert;
use parser::Parser;
use parser::ResultColumn;
use parser::Select;
use parser::Stmt;
use query::Query;
use query::QueryPlan;
use query::RowData;
use record::RecordPayload;
use schema::ColumnNumber;
use schema::Schema;
pub use value::Buffer;
use value::Collation;
use value::TypeAffinity;
pub use value::Value;
use value::ValueCmp;
use value::DEFAULT_COLLATION;

// Original SQLite support both 32-bit or 64-bit rowid. prsqlite only support
// 64-bit rowid.
const MAX_ROWID: i64 = i64::MAX;

#[derive(Debug)]
pub enum Error<'a> {
    Parse(parser::Error<'a>),
    Cursor(cursor::Error),
    Expression(expression::Error),
    Query(query::Error),
    UniqueConstraintViolation,
    DataTypeMismatch,
    Unsupported(&'static str),
    Other(anyhow::Error),
}

impl<'a> From<parser::Error<'a>> for Error<'a> {
    fn from(e: parser::Error<'a>) -> Self {
        Self::Parse(e)
    }
}

impl From<cursor::Error> for Error<'_> {
    fn from(e: cursor::Error) -> Self {
        Self::Cursor(e)
    }
}

impl From<expression::Error> for Error<'_> {
    fn from(e: expression::Error) -> Self {
        Self::Expression(e)
    }
}

impl From<query::Error> for Error<'_> {
    fn from(e: query::Error) -> Self {
        Self::Query(e)
    }
}

impl From<anyhow::Error> for Error<'_> {
    fn from(e: anyhow::Error) -> Self {
        Self::Other(e)
    }
}

impl std::error::Error for Error<'_> {}

impl Display for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Parse(e) => {
                write!(f, "SQL parser error: {}", e)
            }
            Error::Cursor(e) => {
                write!(f, "Btree cursor error: {}", e)
            }
            Error::Expression(e) => {
                write!(f, "expression error: {}", e)
            }
            Error::Query(e) => {
                write!(f, "query error: {}", e)
            }
            Error::DataTypeMismatch => {
                write!(f, "data type mismatch")
            }
            Error::UniqueConstraintViolation => {
                write!(f, "unique constraint violation")
            }
            Error::Unsupported(msg) => {
                write!(f, "unsupported: {}", msg)
            }
            Error::Other(e) => write!(f, "{}", e),
        }
    }
}

pub type Result<'a, T> = std::result::Result<T, Error<'a>>;

pub struct Connection {
    pager: Pager,
    btree_ctx: BtreeContext,
    schema: RefCell<Option<Schema>>,
    /// Number of running read or write.
    ///
    /// > 0 : read(s) running
    /// 0   : no read/write
    /// -1  : write running
    ref_count: Cell<i64>,
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
        header
            .validate()
            .map_err(|e| anyhow::anyhow!("database header invalid: {e}"))?;
        let pagesize = header.pagesize();
        // pagesize is bigger than or equal to 512.
        // reserved is smaller than or equal to 255.
        let usable_size = pagesize - header.reserved() as u32;
        let pager = Pager::new(
            file,
            header.n_pages(),
            pagesize,
            usable_size,
            header.first_freelist_trunk_page_id(),
            header.n_freelist_pages(),
        )?;
        Ok(Self {
            pager,
            btree_ctx: BtreeContext::new(usable_size),
            schema: RefCell::new(None),
            ref_count: Cell::new(0),
        })
    }

    pub fn prepare<'a, 'conn>(&'conn self, sql: &'a str) -> Result<'a, Statement<'conn>> {
        let input = sql.as_bytes();
        let mut parser = Parser::new(input);
        let statement = parse_sql(&mut parser)?;
        expect_semicolon(&mut parser)?;
        expect_no_more_token(&parser)?;

        match statement {
            Stmt::Select(select) => Ok(Statement::Query(self.prepare_select(select)?)),
            Stmt::Insert(insert) => {
                Ok(Statement::Execution(Box::new(self.prepare_insert(insert)?)))
            }
            Stmt::Delete(delete) => {
                Ok(Statement::Execution(Box::new(self.prepare_delete(delete)?)))
            }
        }
    }

    fn load_schema(&self) -> anyhow::Result<()> {
        let schema_table = Schema::schema_table();
        let columns = schema_table
            .get_all_columns()
            .map(Expression::Column)
            .collect::<Vec<_>>();
        *self.schema.borrow_mut() = Some(Schema::generate(
            SelectStatement::new(
                self,
                schema_table.root_page_id,
                columns,
                Expression::one(),
                QueryPlan::FullScan,
            ),
            schema_table,
        )?);
        Ok(())
    }

    fn prepare_select<'a>(&self, select: Select<'a>) -> Result<'a, SelectStatement> {
        if self.schema.borrow().is_none() {
            self.load_schema()?;
        }
        let schema_cell = self.schema.borrow();
        let schema = schema_cell.as_ref().unwrap();
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
            .transpose()?
            .unwrap_or(Expression::one());

        let query_plan = QueryPlan::generate(table, &filter);

        Ok(SelectStatement::new(
            self,
            table.root_page_id,
            columns,
            filter,
            query_plan,
        ))
    }

    fn prepare_insert<'a>(&self, insert: Insert<'a>) -> Result<'a, InsertStatement> {
        if self.schema.borrow().is_none() {
            self.load_schema()?;
        }
        let schema_cell = self.schema.borrow();
        let schema = schema_cell.as_ref().unwrap();
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
            for (column, expr) in columns_idx.iter().zip(column_values) {
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
        let mut indexes = Vec::new();
        let mut index_schema = table.indexes.clone();
        while let Some(index) = index_schema {
            let mut columns = index
                .columns
                .iter()
                .map(|column_number| {
                    let collation = if let ColumnNumber::Column(column_idx) = column_number {
                        &table.columns[*column_idx].collation
                    } else {
                        &DEFAULT_COLLATION
                    };
                    (*column_number, collation.clone())
                })
                .collect::<Vec<_>>();
            columns.push((ColumnNumber::RowId, DEFAULT_COLLATION.clone()));

            indexes.push(IndexSchema {
                root_page_id: index.root_page_id,
                columns,
            });
            index_schema = index.next.clone();
        }
        Ok(InsertStatement {
            conn: self,
            table_page_id,
            records,
            indexes,
        })
    }

    fn prepare_delete<'a>(&self, delete: Delete<'a>) -> Result<'a, DeleteStatement> {
        if self.schema.borrow().is_none() {
            self.load_schema()?;
        }
        let schema_cell = self.schema.borrow();
        let schema = schema_cell.as_ref().unwrap();
        let table_name = delete.table_name.dequote();
        let table = schema.get_table(&table_name).ok_or(anyhow::anyhow!(
            "table not found: {:?}",
            std::str::from_utf8(&table_name).unwrap_or_default()
        ))?;

        let filter = delete
            .filter
            .map(|expr| Expression::from(expr, Some(table)))
            .transpose()?;

        if filter.is_some() {
            todo!("filter");
        }

        let table_page_id = table.root_page_id;
        let mut index_page_ids = Vec::new();
        let mut index_schema = table.indexes.clone();
        while let Some(index) = index_schema {
            index_page_ids.push(index.root_page_id);
            index_schema = index.next.clone();
        }
        Ok(DeleteStatement {
            conn: self,
            table_page_id,
            index_page_ids,
        })
    }

    fn start_read(&self) -> anyhow::Result<ReadTransaction> {
        // TODO: Lock across processes
        let ref_count = self.ref_count.get();
        if ref_count >= 0 {
            self.ref_count.set(ref_count + 1);
            Ok(ReadTransaction(self))
        } else {
            bail!("write statment running");
        }
    }

    fn start_write(&self) -> anyhow::Result<WriteTransaction> {
        // TODO: Lock across processes
        if self.ref_count.get() == 0 {
            self.ref_count.set(-1);
            Ok(WriteTransaction {
                conn: self,
                do_commit: false,
            })
        } else {
            bail!("other statments running");
        }
    }
}

struct ReadTransaction<'a>(&'a Connection);

impl Drop for ReadTransaction<'_> {
    fn drop(&mut self) {
        self.0.ref_count.set(self.0.ref_count.get() - 1);
    }
}

struct WriteTransaction<'a> {
    conn: &'a Connection,
    do_commit: bool,
}

impl WriteTransaction<'_> {
    fn commit(mut self) -> anyhow::Result<()> {
        if self.conn.pager.is_file_size_changed() {
            let page1 = self.conn.pager.get_page(PAGE_ID_1)?;
            let mut buffer = self.conn.pager.make_page_mut(&page1)?;
            let header_buf = &mut buffer[..DATABASE_HEADER_SIZE];
            let mut header = DatabaseHeaderMut::from(header_buf.try_into().unwrap());
            header.set_n_pages(self.conn.pager.num_pages());
            drop(buffer);
            drop(page1);
        }

        self.conn.pager.commit()?;
        self.do_commit = true;
        Ok(())
    }
}

impl Drop for WriteTransaction<'_> {
    fn drop(&mut self) {
        if !self.do_commit {
            self.conn.pager.abort();
        }
        self.conn.ref_count.set(0);
    }
}

pub trait ExecutionStatement {
    fn execute(&self) -> Result<u64>;
}

pub enum Statement<'conn> {
    Query(SelectStatement<'conn>),
    Execution(Box<dyn ExecutionStatement + 'conn>),
}

impl<'conn> Statement<'conn> {
    pub fn query(&'conn self) -> anyhow::Result<Rows<'conn>> {
        match self {
            Self::Query(stmt) => stmt.query(),
            Self::Execution(_) => bail!("execute statement not support query"),
        }
    }

    pub fn execute(&'conn self) -> Result<u64> {
        match self {
            Self::Query(_) => Err(Error::Unsupported("select statement not support execute")),
            Self::Execution(stmt) => stmt.execute(),
        }
    }
}

pub struct SelectStatement<'conn> {
    conn: &'conn Connection,
    table_page_id: PageId,
    columns: Vec<Expression>,
    filter: Expression,
    query_plan: QueryPlan,
}

impl<'conn> SelectStatement<'conn> {
    pub(crate) fn new(
        conn: &'conn Connection,
        table_page_id: PageId,
        columns: Vec<Expression>,
        filter: Expression,
        query_plan: QueryPlan,
    ) -> Self {
        Self {
            conn,
            table_page_id,
            columns,
            filter,
            query_plan,
        }
    }

    pub fn query(&'conn self) -> anyhow::Result<Rows<'conn>> {
        let read_txn = self.conn.start_read()?;
        // TODO: check schema version.

        let query = Query::new(
            self.table_page_id,
            &self.conn.pager,
            &self.conn.btree_ctx,
            &self.query_plan,
            &self.filter,
        )?;

        Ok(Rows {
            _read_txn: read_txn,
            stmt: self,
            query,
        })
    }
}

pub struct Rows<'conn> {
    _read_txn: ReadTransaction<'conn>,
    stmt: &'conn SelectStatement<'conn>,
    query: Query<'conn>,
}

impl<'conn> Rows<'conn> {
    pub fn next_row(&mut self) -> Result<Option<Row<'_>>> {
        if let Some(data) = self.query.next()? {
            Ok(Some(Row {
                stmt: self.stmt,
                data,
            }))
        } else {
            Ok(None)
        }
    }
}

pub struct Row<'a> {
    stmt: &'a SelectStatement<'a>,
    data: RowData<'a>,
}

impl<'a> Row<'a> {
    pub fn parse(&self) -> Result<Columns<'_>> {
        let mut columns = Vec::with_capacity(self.stmt.columns.len());
        for expr in self.stmt.columns.iter() {
            let (value, _, _) = expr.execute(Some(&self.data))?;
            columns.push(value);
        }
        Ok(Columns(columns))
    }
}

pub struct Columns<'a>(Vec<Option<Value<'a>>>);

impl<'a> Columns<'a> {
    pub fn get(&self, i: usize) -> Option<&Value<'a>> {
        if let Some(Some(v)) = self.0.get(i) {
            Some(v)
        } else {
            None
        }
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &Option<Value<'a>>> {
        self.0.iter()
    }
}

struct InsertRecord {
    rowid: Option<Expression>,
    columns: Vec<(Expression, TypeAffinity)>,
}

struct IndexSchema {
    root_page_id: PageId,
    columns: Vec<(ColumnNumber, Collation)>,
}

pub struct InsertStatement<'conn> {
    conn: &'conn Connection,
    table_page_id: PageId,
    records: Vec<InsertRecord>,
    indexes: Vec<IndexSchema>,
}

impl<'conn> ExecutionStatement for InsertStatement<'conn> {
    fn execute(&self) -> Result<u64> {
        let write_txn = self.conn.start_write()?;

        let mut cursor =
            BtreeCursor::new(self.table_page_id, &self.conn.pager, &self.conn.btree_ctx)?;
        let mut n = 0;
        for record in self.records.iter() {
            let mut rowid = None;
            if let Some(rowid_expr) = &record.rowid {
                let (rowid_value, _, _) = rowid_expr.execute::<RowData>(None)?;
                // NULL then fallback to generate new rowid.
                if let Some(rowid_value) = rowid_value {
                    match rowid_value.apply_numeric_affinity() {
                        Value::Integer(rowid_value) => {
                            rowid = Some(rowid_value);
                        }
                        _ => return Err(Error::DataTypeMismatch),
                    }
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
                return Err(Error::UniqueConstraintViolation);
            }

            let mut columns = Vec::with_capacity(record.columns.len());
            for (expr, type_affinity) in record.columns.iter() {
                let (value, _, _) = expr.execute::<RowData>(None)?;
                let value = value.map(|v| v.apply_affinity(*type_affinity));
                columns.push(value);
            }

            cursor.table_insert(
                rowid,
                &RecordPayload::new(&columns.iter().map(|v| v.as_ref()).collect::<Vec<_>>())?,
            )?;

            let row_id = Value::Integer(rowid);
            for index in self.indexes.iter() {
                let index_columns = index
                    .columns
                    .iter()
                    .map(|(column_number, _)| match column_number {
                        ColumnNumber::RowId => Some(&row_id),
                        ColumnNumber::Column(column_idx) => columns[*column_idx].as_ref(),
                    })
                    .collect::<Vec<_>>();
                let comparators = index
                    .columns
                    .iter()
                    .zip(index_columns.iter())
                    .map(|((_, collation), v)| v.map(|v| ValueCmp::new(v, collation)))
                    .collect::<Vec<_>>();
                let mut index_cursor =
                    BtreeCursor::new(index.root_page_id, &self.conn.pager, &self.conn.btree_ctx)?;
                index_cursor.index_insert(&comparators, &RecordPayload::new(&index_columns)?)?;
            }

            n += 1;
        }

        write_txn.commit()?;

        Ok(n)
    }
}

pub struct DeleteStatement<'conn> {
    conn: &'conn Connection,
    table_page_id: PageId,
    index_page_ids: Vec<PageId>,
}

impl<'conn> ExecutionStatement for DeleteStatement<'conn> {
    fn execute(&self) -> Result<u64> {
        let write_txn = self.conn.start_write()?;

        let mut cursor =
            BtreeCursor::new(self.table_page_id, &self.conn.pager, &self.conn.btree_ctx)?;

        let n_deleted = cursor.clear()?;

        for index_page_id in self.index_page_ids.iter() {
            let mut cursor =
                BtreeCursor::new(*index_page_id, &self.conn.pager, &self.conn.btree_ctx)?;
            let n = cursor.clear()?;
            if n != n_deleted {
                return Err(Error::Other(anyhow::anyhow!(
                    "number of deleted rows in table and index does not match"
                )));
            }
        }

        write_txn.commit()?;

        Ok(n_deleted)
    }
}
