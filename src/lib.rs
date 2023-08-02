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

use std::fs::File;
use std::os::unix::fs::FileExt;
use std::path::Path;

use anyhow::bail;
use anyhow::Context;

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
use crate::record::SerialType;
pub use crate::record::Value;
use crate::schema::ColumnIndex;
use crate::schema::Schema;
use crate::schema::Table;
use crate::token::get_token_no_space;
use crate::token::Token;

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
        let (n, select) = parse_select(input).map_err(|e| anyhow::anyhow!("parse select: {}", e))?;
        if let Some((nn, Token::Semicolon)) = get_token_no_space(&input[n..]) {
            if nn + n != input.len() {
                bail!("extra characters after semicolon");
            }
        } else {
            bail!("no semicolon");
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
        let table = schema.get_table(select.table_name).ok_or(anyhow::anyhow!(
            "table not found: {:?}",
            std::str::from_utf8(select.table_name).unwrap_or_default()
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
                    let column_idx = table.get_column_index(column_name).ok_or(anyhow::anyhow!(
                        "column not found: {}",
                        std::str::from_utf8(column_name).unwrap_or_default()
                    ))?;
                    columns.push(column_idx);
                }
            }
        }

        let selection = select.selection.map(|expr| Selection::from(expr, table)).transpose()?;

        let table_page_id = table.root_page_id;
        Ok(Statement::new(self, table_page_id, columns, selection))
    }
}

enum Selection {
    Column(ColumnIndex),
    BinaryOperator {
        operator: BinaryOperator,
        left: Box<Selection>,
        right: Box<Selection>,
    },
    LiteralValue(i64),
}

impl Selection {
    fn execute(&self, row: &Row) -> anyhow::Result<i64> {
        match self {
            Self::Column(idx) => {
                let value = row.get_column(idx)?;
                match value {
                    Value::Integer(i) => Ok(i),
                    _ => bail!("invalid value for selection: {:?}", value),
                }
            }
            Self::BinaryOperator { operator, left, right } => {
                let left = left.execute(row)?;
                let right = right.execute(row)?;
                let result = match operator {
                    BinaryOperator::Eq => left == right,
                    BinaryOperator::Ne => left != right,
                    BinaryOperator::Lt => left < right,
                    BinaryOperator::Le => left <= right,
                    BinaryOperator::Gt => left > right,
                    BinaryOperator::Ge => left >= right,
                };
                if result {
                    Ok(1)
                } else {
                    Ok(0)
                }
            }
            Self::LiteralValue(value) => Ok(*value),
        }
    }
}

impl Selection {
    fn from(expr: Expr, table: &Table) -> anyhow::Result<Self> {
        match expr {
            Expr::LiteralValue(value) => match value {
                Value::Integer(i) => Ok(Self::LiteralValue(i)),
                _ => bail!("unsupported literal value: {:?}", value),
            },
            Expr::BinaryOperator { operator, left, right } => Ok(Self::BinaryOperator {
                operator,
                left: Box::new(Self::from(*left, table)?),
                right: Box::new(Self::from(*right, table)?),
            }),
            Expr::Column(column_name) => table
                .get_column_index(column_name)
                .map(Self::Column)
                .ok_or(anyhow::anyhow!(
                    "column not found: {}",
                    std::str::from_utf8(column_name).unwrap_or_default()
                )),
        }
    }
}

// TODO: make Connection non mut and support multiple statements.
pub struct Statement<'conn> {
    conn: &'conn mut Connection,
    table_page_id: u32,
    columns: Vec<ColumnIndex>,
    selection: Option<Selection>,
    rowid: Option<i64>,
}

impl<'conn> Statement<'conn> {
    pub(crate) fn new(
        conn: &'conn mut Connection,
        table_page_id: u32,
        columns: Vec<ColumnIndex>,
        selection: Option<Selection>,
    ) -> Self {
        let rowid = match &selection {
            Some(Selection::BinaryOperator {
                operator: BinaryOperator::Eq,
                left,
                right,
            }) => match (left.as_ref(), right.as_ref()) {
                (Selection::Column(ColumnIndex::RowId), Selection::LiteralValue(value)) => Some(*value),
                (Selection::LiteralValue(value), Selection::Column(ColumnIndex::RowId)) => Some(*value),
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
        }
    }

    pub fn execute(&'conn mut self) -> anyhow::Result<Rows<'conn>> {
        // TODO: check schema version.
        let mut cursor = BtreeCursor::new(self.table_page_id, &self.conn.pager, &self.conn.btree_ctx)?;
        if let Some(rowid) = self.rowid {
            cursor.move_to(rowid)?;
        }
        Ok(Rows {
            stmt: self,
            cursor,
            completed: false,
        })
    }
}

pub struct Rows<'conn> {
    stmt: &'conn Statement<'conn>,
    cursor: BtreeCursor<'conn, 'conn>,
    completed: bool,
}

/// TODO: Skip should be encapuslated inside [Rows::next]. However we need this due to Rust borrow checker limitation.
/// This is a workaround for the limitation. This is fixed with `RUSTFLAGS="-Zpolonius"`. polonius is a new borrow
/// checker but not settled yet.
///
/// With original `continue` implementation, we get this error:
///
/// ```text
/// error[E0499]: cannot borrow `self.cursor` as mutable more than once at a time
///    --> src/lib.rs:295:35
///    |
/// 294 |       pub fn next<'a>(&'a mut self) -> anyhow::Result<NextRow<'a, 'conn>> {
///    |                   -- lifetime `'a` defined here
/// 295 |           while let Some(payload) = self.cursor.next()? {
///    |                                     ^^^^^^^^^^^^^^^^^^ `self.cursor` was mutably borrowed here in the previous iteration of the loop
/// ...
/// 299 |                   return Ok(NextRow::Row(Row {
///    |  ________________________-
/// 300 | |                     stmt: self.stmt,
/// 301 | |                     payload,
/// 302 | |                     headers,
/// ...   |
/// 305 | |                     tmp_buf: Vec::new(),
/// 306 | |                 }));
///    | |___________________- returning this value requires that `self.cursor` is borrowed for `'a`
/// ```
///
/// PoC: https://play.rust-lang.org/?version=stable&mode=debug&edition=2021&gist=0f11c057d716d62ac2f56c90dcf52512
/// Link: https://users.rust-lang.org/t/mutably-borrowed-in-previous-iteration-despite-no-chance-of-conflicting-borrow/83274
pub enum NextRow<'a, 'conn> {
    Some(Row<'a, 'conn>),
    Skip,
    None,
}

impl<'a, 'conn> NextRow<'a, 'conn> {
    pub fn unwrap(self) -> Row<'a, 'conn> {
        match self {
            Self::Some(row) => row,
            Self::Skip => panic!("called `NextRow::unwrap()` on a `Skip` value"),
            Self::None => panic!("called `NextRow::unwrap()` on a `None` value"),
        }
    }

    pub fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }
}

impl<'conn> Rows<'conn> {
    pub fn next<'a>(&'a mut self) -> anyhow::Result<NextRow<'a, 'conn>> {
        if self.completed {
            return Ok(NextRow::None);
        } else if self.stmt.rowid.is_some() {
            // Only one row is selected.
            self.completed = true;
        }
        // TODO: Keep this never_loop to make it clear that [NextRow] is a workaround for borrow checker limitation.
        #[allow(clippy::never_loop)]
        while let Some(payload) = self.cursor.next()? {
            let headers = parse_record_header(&payload)?;

            if headers.is_empty() {
                return Ok(NextRow::Some(Row {
                    stmt: self.stmt,
                    payload,
                    headers,
                    content_offset: 0,
                    use_local_buffer: true,
                    tmp_buf: Vec::new(),
                }));
            }

            let content_offset = headers[0].1;
            let last_header = &headers[headers.len() - 1];
            let content_size = last_header.1 + last_header.0.content_size() - content_offset;
            let use_local_buffer = payload.buf().len() >= (content_offset + content_size) as usize;
            let mut tmp_buf;
            if use_local_buffer {
                tmp_buf = Vec::new();
            } else {
                tmp_buf = vec![0; content_size as usize];
                let n = unsafe { payload.load(content_offset, &mut tmp_buf) }?;
                if n != content_size as usize {
                    bail!("payload does not have enough size");
                }
            };

            let row = Row {
                stmt: self.stmt,
                headers,
                payload,
                content_offset,
                use_local_buffer,
                tmp_buf,
            };

            if let Some(selection) = &self.stmt.selection {
                if selection.execute(&row)? == 0 {
                    // TODO: continue is what we want. However Rust borrow checker does not allow it by accident.
                    // See the comment of [NextRow] for more details.

                    // continue;
                    return Ok(NextRow::Skip);
                }
            }

            return Ok(NextRow::Some(row));
        }
        Ok(NextRow::None)
    }
}

const STATIC_NULL_VALUE: Value = Value::Null;

pub struct Row<'a, 'conn> {
    stmt: &'a Statement<'conn>,
    pub payload: BtreePayload<'a, 'conn>,
    headers: Vec<(SerialType, i32)>,
    content_offset: i32,
    use_local_buffer: bool,
    tmp_buf: Vec<u8>,
}

impl<'a, 'conn> Row<'a, 'conn> {
    pub fn parse(&self) -> anyhow::Result<Columns> {
        let mut columns = Vec::with_capacity(self.stmt.columns.len());
        for column_idx in self.stmt.columns.iter() {
            columns.push(self.get_column(column_idx)?);
        }

        Ok(Columns(columns))
    }

    fn get_column(&self, column_idx: &ColumnIndex) -> anyhow::Result<Value> {
        match column_idx {
            ColumnIndex::Column(idx) => {
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
            ColumnIndex::RowId => Ok(Value::Integer(self.payload.key())),
        }
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
