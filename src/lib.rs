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
pub use crate::btree::*;
use crate::cursor::BtreeCursor;
use crate::cursor::BtreePayload;
use crate::pager::Pager;
use crate::parser::parse_select;
use crate::parser::ResultColumn;
use crate::record::parse_record_header;
pub use crate::record::Value;
use crate::schema::Schema;
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

    pub fn usable_size(&self) -> u32 {
        self.pagesize() - self.reserved() as u32
    }
}

pub struct Connection {
    pager: Pager,
    usable_size: u32,
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
            usable_size: header.usable_size(),
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
            let columns = (0..schema_table.columns.len()).collect::<Vec<usize>>();
            self.schema = Some(Schema::generate(
                Statement::new(self, schema_table.root_page_id, columns),
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
                    for i in 0..table.columns.len() {
                        columns.push(i);
                    }
                }
                ResultColumn::ColumnName(column_name) => {
                    let column_idx = table
                        .columns
                        .iter()
                        .position(|c| c == column_name)
                        .ok_or(anyhow::anyhow!(
                            "column not found: {}",
                            std::str::from_utf8(column_name).unwrap_or_default()
                        ))?;
                    columns.push(column_idx);
                }
            }
        }

        let table_page_id = table.root_page_id;
        Ok(Statement::new(self, table_page_id, columns))
    }
}

// TODO: make Connection non mut and support multiple statements.
pub struct Statement<'conn> {
    conn: &'conn mut Connection,
    table_page_id: u32,
    columns: Vec<usize>,
}

impl<'conn> Statement<'conn> {
    pub(crate) fn new(conn: &'conn mut Connection, table_page_id: u32, columns: Vec<usize>) -> Self {
        Self {
            conn,
            table_page_id,
            columns,
        }
    }

    pub fn execute(&'conn mut self) -> anyhow::Result<Rows<'conn>> {
        // TODO: check schema version.
        Ok(Rows {
            stmt: self,
            cursor: BtreeCursor::new(self.table_page_id, &self.conn.pager, self.conn.usable_size)?,
        })
    }
}

pub struct Rows<'conn> {
    stmt: &'conn Statement<'conn>,
    cursor: BtreeCursor<'conn>,
}

impl<'conn> Rows<'conn> {
    pub fn next<'a>(&'a mut self) -> anyhow::Result<Option<Row<'a, 'conn>>> {
        Ok(self.cursor.next()?.map(|payload| Row {
            stmt: self.stmt,
            payload,
            tmp_buf: Vec::new(),
        }))
    }
}

const STATIC_NULL_VALUE: Value = Value::Null;

pub struct Row<'a, 'conn> {
    stmt: &'conn Statement<'conn>,
    pub payload: BtreePayload<'a, 'conn>,
    tmp_buf: Vec<u8>,
}

impl<'a, 'conn> Row<'a, 'conn> {
    pub fn parse(&mut self) -> anyhow::Result<Columns> {
        let headers = parse_record_header(&self.payload)?;

        if headers.is_empty() {
            return Ok(Columns(Vec::new()));
        }

        let content_offset = headers[0].1;
        let last_header = &headers[headers.len() - 1];
        let content_size = last_header.1 + last_header.0.content_size() - content_offset;
        let contents_buffer = if self.payload.buf().len() >= (content_offset + content_size) as usize {
            &self.payload.buf()[content_offset as usize..]
        } else {
            self.tmp_buf = vec![0; content_size as usize];
            let n = unsafe { self.payload.load(content_offset, &mut self.tmp_buf) }?;
            if n != content_size as usize {
                bail!("payload does not have enough size");
            }
            &self.tmp_buf
        };

        let mut columns = Vec::with_capacity(self.stmt.columns.len());
        for column_idx in self.stmt.columns.iter() {
            if let Some((serial_type, offset)) = headers.get(*column_idx) {
                columns.push(
                    serial_type
                        .parse(&contents_buffer[(offset - content_offset) as usize..])
                        .context("parse value")?,
                );
            } else {
                columns.push(STATIC_NULL_VALUE);
            }
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
