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

use std::collections::HashMap;
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

fn parse_table_name(sql: &str) -> anyhow::Result<String> {
    let chars = sql.chars();
    let mut table_name = String::new();
    for c in chars {
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
        const SELECT_PREFIX: &str = "SELECT * FROM ";
        if let Some(sql) = sql.strip_prefix(SELECT_PREFIX) {
            let table = parse_table_name(sql)?;
            Ok(Statement { conn: self, table })
        } else {
            bail!("Unsupported SQL: {}", sql);
        }
    }
}

struct Schema {
    tables: HashMap<String, Table>,
}

impl Schema {
    fn generate(pager: &Pager, usable_size: u32) -> anyhow::Result<Schema> {
        let mut rows = Rows {
            cursor: BtreeCursor::new(ROOT_PAGE_ID, pager, usable_size)?,
        };
        let mut tables = HashMap::new();
        while let Some(mut row) = rows.next()? {
            let columns = row.parse()?;
            match columns.get(0) {
                &Value::Text("table") => {
                    if columns.get(1) != columns.get(2) {
                        bail!(
                            "table name does not match: name={:?}, table_name={:?}",
                            columns.get(1),
                            columns.get(2)
                        );
                    }
                    if let &Value::Text(table) = columns.get(1) {
                        if let &Value::Integer(page_id) = columns.get(3) {
                            tables.insert(
                                table.to_string(),
                                Table {
                                    root_page_id: page_id.try_into()?,
                                },
                            );
                        }
                    }
                }
                &Value::Text("index") => {
                    // TODO: support index
                }
                &Value::Text("view") => {
                    // TODO: support view
                }
                &Value::Text("trigger") => {
                    // TODO: support trigger
                }
                type_ => {
                    bail!("unsupported type: {:?}", type_);
                }
            }
        }
        Ok(Self { tables })
    }

    fn get_table_page_id(&self, table: &str) -> Option<PageId> {
        self.tables.get(table).map(|table| table.root_page_id)
    }
}

struct Table {
    root_page_id: PageId,
}

// TODO: make Connection non mut and support multiple statements.
pub struct Statement<'conn> {
    conn: &'conn mut Connection,
    table: String,
}

impl<'conn> Statement<'conn> {
    pub fn execute(&'conn mut self) -> anyhow::Result<Rows<'conn>> {
        if self.conn.schema.is_none() {
            self.conn.schema = Some(Schema::generate(&self.conn.pager, self.conn.usable_size)?);
        }
        let schema = self.conn.schema.as_ref().unwrap();
        let table_page_id = if let Some(table_page_id) = schema.get_table_page_id(&self.table) {
            table_page_id
        } else {
            bail!("table not found: {}", self.table);
        };
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
    pub fn parse(&mut self) -> anyhow::Result<Columns> {
        let headers = parse_record_header(&self.payload)?;

        if headers.is_empty() {
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
    fn get_table_page_id_success() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE TABLE example2(col1, col2);",
            "CREATE TABLE example3(col1, col2, col3);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let usable_size = load_usable_size(file.as_file()).unwrap();

        let schema = Schema::generate(&pager, usable_size).unwrap();
        let page_id = schema.get_table_page_id("example2").unwrap();

        assert_eq!(page_id, 3);
    }

    #[test]
    fn get_table_page_id_interior_success() {
        let mut queries = Vec::with_capacity(100);
        for i in 0..100 {
            queries.push(format!(
                "CREATE TABLE example{i}(col1,col2,col3,col4,col5,col6,col7,col8,col9,col10);"
            ));
        }
        let file =
            create_sqlite_database(&queries.iter().map(|q| q.as_str()).collect::<Vec<&str>>());
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        assert!(pager.num_pages() > 1);
        let usable_size = load_usable_size(file.as_file()).unwrap();

        let schema = Schema::generate(&pager, usable_size).unwrap();
        let page_id = schema.get_table_page_id("example99").unwrap();

        assert_eq!(page_id, 104);
    }

    #[test]
    fn get_table_page_id_not_found() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE TABLE example2(col1, col2);",
            "CREATE TABLE example3(col1, col2, col3);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let usable_size = load_usable_size(file.as_file()).unwrap();

        let schema = Schema::generate(&pager, usable_size).unwrap();

        assert!(schema.get_table_page_id("invalid").is_none());
    }
}
