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
mod record;
#[cfg(test)]
pub mod test_utils;
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
use crate::pager::PageId;
use crate::pager::Pager;
use crate::pager::ROOT_PAGE_ID;
use crate::record::parse_record_header;
pub use crate::record::Value;

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
        pagesize >= 512 && pagesize <= SQLITE_MAX_PAGE_SIZE && (pagesize - 1) & pagesize == 0
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

fn parse_table_name(sql: &str) -> anyhow::Result<String> {
    let mut chars = sql.chars();
    let mut table_name = String::new();
    while let Some(c) = chars.next() {
        if c.is_whitespace() || c == ';' {
            break;
        }
        if c.is_ascii_alphanumeric() {
            table_name.push(c);
        } else {
            bail!("invalid table name: {}", sql);
        }
    }
    Ok(table_name)
}

pub struct Connection {
    pager: Pager,
    usable_size: u32,
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
        })
    }

    pub fn prepare(&self, sql: &str) -> anyhow::Result<Statement> {
        const SELECT_PREFIX: &str = "SELECT * FROM ";
        if sql.starts_with(SELECT_PREFIX) {
            let table = parse_table_name(&sql[SELECT_PREFIX.len()..])?;
            Ok(Statement { conn: self, table })
        } else {
            bail!("Unsupported SQL: {}", sql);
        }
    }
}

pub struct Statement<'conn> {
    conn: &'conn Connection,
    table: String,
}

impl<'conn> Statement<'conn> {
    pub fn execute(&mut self) -> anyhow::Result<Rows<'conn>> {
        let table_page_id = find_table_page_id(
            self.table.as_bytes(),
            &self.conn.pager,
            self.conn.usable_size,
        )?;
        Ok(Rows {
            cursor: BtreeCursor::new(table_page_id, &self.conn.pager, self.conn.usable_size)?,
        })
    }
}

pub struct Rows<'conn> {
    cursor: BtreeCursor<'conn>,
}

impl<'conn> Rows<'conn> {
    pub fn next<'a>(&'a mut self) -> anyhow::Result<Option<Row<'a, 'conn>>> {
        Ok(self.cursor.next()?.map(|payload| Row {
            payload,
            tmp_buf: Vec::new(),
        }))
    }
}

const STATIC_NULL_VALUE: Value = Value::Null;

pub struct Row<'a, 'conn> {
    pub payload: BtreePayload<'a, 'conn>,
    tmp_buf: Vec<u8>,
}

impl<'a, 'conn> Row<'a, 'conn> {
    pub fn parse<'b>(&'b mut self) -> anyhow::Result<Columns<'b>> {
        let headers = parse_record_header(&self.payload)?;

        if headers.len() == 0 {
            return Ok(Columns(Vec::new()));
        }

        let content_offset = headers[0].1;
        let last_header = &headers[headers.len() - 1];
        let content_size = last_header.1 + last_header.0.content_size() - content_offset;
        let contents_buffer =
            if self.payload.buf().len() >= (content_offset + content_size) as usize {
                &self.payload.buf()[content_offset as usize..]
            } else {
                self.tmp_buf = vec![0; content_size as usize];
                let n = unsafe { self.payload.load(content_offset, &mut self.tmp_buf) }?;
                if n != content_size as usize {
                    bail!("payload does not have enough size");
                }
                &self.tmp_buf
            };

        let mut columns = Vec::with_capacity(headers.len());
        for (serial_type, offset) in headers {
            columns.push(
                serial_type
                    .parse(&contents_buffer[(offset - content_offset) as usize..])
                    .context("parse value")?,
            );
        }

        Ok(Columns(columns))
    }
}

pub struct Columns<'a>(Vec<Value<'a>>);

impl<'a> Columns<'a> {
    pub fn get(&self, i: usize) -> &Value<'a> {
        self.0.get(i).unwrap_or(&STATIC_NULL_VALUE)
    }
}

pub fn find_table_page_id<'a>(
    table: &[u8],
    pager: &'a Pager,
    usable_size: u32,
) -> anyhow::Result<PageId> {
    let mut rows = Rows {
        cursor: BtreeCursor::new(ROOT_PAGE_ID, pager, usable_size)?,
    };
    while let Some(mut row) = rows.next()? {
        let columns = row.parse()?;
        if columns.get(0) == &Value::Text(b"table") && columns.get(1) == &Value::Text(table) {
            if let &Value::Integer(page_id) = columns.get(3) {
                return Ok(page_id.try_into()?);
            } else {
                bail!("invalid root page id");
            }
        }
    }
    bail!("table not found");
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

    #[test]
    fn find_table_page_id_success() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE TABLE example2(col1, col2);",
            "CREATE TABLE example3(col1, col2, col3);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let usable_size = load_usable_size(file.as_file()).unwrap();

        let page_id = find_table_page_id(b"example2", &pager, usable_size).unwrap();

        assert_eq!(page_id, 3);
    }

    #[test]
    fn find_table_page_id_interior_success() {
        let mut queries = Vec::with_capacity(100);
        for i in 0..100 {
            queries.push(format!(
                "CREATE TABLE example{}(col1,col2,col3,col4,col5,col6,col7,col8,col9,col10);",
                i
            ));
        }
        let file =
            create_sqlite_database(&queries.iter().map(|q| q.as_str()).collect::<Vec<&str>>());
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let usable_size = load_usable_size(file.as_file()).unwrap();

        let page_id = find_table_page_id(b"example99", &pager, usable_size).unwrap();

        assert_eq!(page_id, 104);
    }

    #[test]
    fn find_table_not_found() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE TABLE example2(col1, col2);",
            "CREATE TABLE example3(col1, col2, col3);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let usable_size = load_usable_size(file.as_file()).unwrap();

        let result = find_table_page_id(b"invalid", &pager, usable_size);

        assert!(result.is_err());
    }
}
