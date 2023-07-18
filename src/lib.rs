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
#[cfg(test)]
pub mod test_utils;
mod utils;

use std::fs::File;
use std::os::unix::fs::FileExt;
use std::path::Path;

use anyhow::bail;
use cursor::BtreePayload;
use thiserror::Error as ThisError;

// TODO: This is to suppress the unused warning.
pub use crate::btree::*;
use crate::cursor::BtreeCursor;
use crate::pager::PageId;
use crate::pager::Pager;
use crate::pager::ROOT_PAGE_ID;
use crate::utils::parse_varint;
use crate::utils::unsafe_parse_varint;

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

const STATIC_NULL_RECORD: Record = Record::Null;

pub struct Row<'a, 'conn> {
    pub payload: BtreePayload<'a, 'conn>,
    tmp_buf: Vec<u8>,
}

impl<'a, 'conn> Row<'a, 'conn> {
    pub fn parse<'b>(&'b mut self) -> anyhow::Result<Records<'b>> {
        let payload = if self.payload.buf().len() as u32 == self.payload.size() {
            self.payload.buf()
        } else {
            self.tmp_buf = vec![0; self.payload.size() as usize];
            let n = unsafe { self.payload.load(0, &mut self.tmp_buf) }?;
            if n != self.payload.size() as usize {
                bail!("payload does not have enough size");
            }
            &self.tmp_buf[..n]
        };

        let (header_size, consumed) =
            parse_varint(payload).ok_or_else(|| anyhow::anyhow!("invalid header size"))?;
        let header_size: usize = header_size.try_into()?;
        if header_size > payload.len() || header_size < consumed {
            bail!("invalid payload header size");
        }
        let mut headers = &payload[consumed..header_size];
        let mut contents = &payload[header_size..];
        let mut records = Vec::new();
        while headers.len() > 0 {
            let (r, h, c) = parse_record(headers, contents);
            records.push(r);
            headers = h;
            contents = c;
        }
        assert!(headers.len() == 0);
        if contents.len() > 0 {
            bail!("payload contents is too big");
        }

        Ok(Records(records))
    }
}

pub struct Records<'a>(Vec<Record<'a>>);

impl<'a> Records<'a> {
    pub fn get(&self, i: usize) -> &Record<'a> {
        self.0.get(i).unwrap_or(&STATIC_NULL_RECORD)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Record<'a> {
    Null,
    Int8(&'a [u8; 1]),
    Int16(&'a [u8; 2]),
    Int24(&'a [u8; 3]),
    Int32(&'a [u8; 4]),
    Int48(&'a [u8; 6]),
    Int64(&'a [u8; 8]),
    Float64(&'a [u8; 8]),
    Zero,
    One,
    Reserved,
    Blob(&'a [u8]),
    Text(&'a [u8]),
}

// TODO: automatic type conversion
impl<'a> Record<'a> {
    pub fn to_i64(&self) -> anyhow::Result<i64> {
        use Record::*;
        match *self {
            Int8(buf) => Ok(i8::from_be_bytes(*buf) as i64),
            Int16(buf) => Ok(i16::from_be_bytes(*buf) as i64),
            // TODO: use std::mem::transmute.
            Int24(buf) => {
                Ok(((buf[0] as i64) << 56 | (buf[1] as i64) << 48 | (buf[2] as i64) << 40) >> 40)
            }
            Int32(buf) => Ok(i32::from_be_bytes(*buf) as i64),
            // TODO: use std::mem::transmute.
            Int48(buf) => Ok(((buf[0] as i64) << 56
                | (buf[1] as i64) << 48
                | (buf[2] as i64) << 40
                | (buf[3] as i64) << 32
                | (buf[4] as i64) << 24
                | (buf[5] as i64) << 16)
                >> 16),
            Int64(buf) => Ok(i64::from_be_bytes(*buf)),
            Zero => Ok(0),
            One => Ok(1),
            _ => Err(anyhow::anyhow!("unexpected type")),
        }
    }

    pub fn to_f64(&self) -> anyhow::Result<f64> {
        use Record::*;
        match *self {
            Float64(buf) => Ok(f64::from_be_bytes(*buf)),
            _ => Err(anyhow::anyhow!("unexpected type")),
        }
    }

    pub fn to_bool(&self) -> anyhow::Result<bool> {
        use Record::*;
        match *self {
            Zero => Ok(false),
            One => Ok(true),
            _ => Err(anyhow::anyhow!("unexpected type")),
        }
    }

    pub fn to_slice(&self) -> anyhow::Result<&'a [u8]> {
        use Record::*;
        match *self {
            Blob(buf) => Ok(buf),
            Text(buf) => Ok(buf),
            _ => Err(anyhow::anyhow!("unexpected type")),
        }
    }

    pub fn is_null(&self) -> bool {
        use Record::*;
        match *self {
            Null => true,
            _ => false,
        }
    }
}

pub fn parse_record<'a>(headers: &'a [u8], contents: &'a [u8]) -> (Record<'a>, &'a [u8], &'a [u8]) {
    let (serial_type, consumed) = unsafe_parse_varint(headers);
    let headers = &headers[consumed..];
    match serial_type {
        0 => (Record::Null, headers, contents),
        1 => (
            Record::Int8(contents[..1].try_into().unwrap()),
            headers,
            &contents[1..],
        ),
        2 => (
            Record::Int16(contents[..2].try_into().unwrap()),
            headers,
            &contents[2..],
        ),
        3 => (
            Record::Int24(contents[..3].try_into().unwrap()),
            headers,
            &contents[3..],
        ),
        4 => (
            Record::Int32(contents[..4].try_into().unwrap()),
            headers,
            &contents[4..],
        ),
        5 => (
            Record::Int48(contents[..6].try_into().unwrap()),
            headers,
            &contents[6..],
        ),
        6 => (
            Record::Int64(contents[..8].try_into().unwrap()),
            headers,
            &contents[8..],
        ),
        7 => (
            Record::Float64(contents[..8].try_into().unwrap()),
            headers,
            &contents[8..],
        ),
        8 => (Record::Zero, headers, contents),
        9 => (Record::One, headers, contents),
        10 | 11 => {
            unimplemented!("reserved record is not implemented");
            // (Record::Reserved,&header[serial_size..],content)
        }
        n if n & 1 == 0 => {
            let size = ((n - 12) >> 1) as usize;
            (Record::Blob(&contents[..size]), headers, &contents[size..])
        }
        n => {
            let size = ((n - 13) >> 1) as usize;
            (Record::Text(&contents[..size]), headers, &contents[size..])
        }
    }
}

#[derive(ThisError, Debug)]
pub enum Error {
    #[error("failed to parse: {0}")]
    ParseField(&'static str),
}

pub fn parse_records<'a>(payload: &'a [u8], records: &mut [Record<'a>]) -> anyhow::Result<usize> {
    let (header_size, consumed) = unsafe_parse_varint(payload);
    let header_size: usize = header_size.try_into().unwrap();
    let mut headers = &payload[consumed..header_size];
    let mut contents = &payload[header_size..];
    let mut i: usize = 0;
    while headers.len() > 0 && i < records.len() {
        let (r, h, c) = parse_record(headers, contents);
        records[i] = r;
        headers = h;
        contents = c;
        i += 1;
    }
    assert!(headers.len() == 0);
    assert!(contents.len() == 0);
    Ok(i)
}
pub struct SQLiteSchema<'a> {
    pub _type: &'a [u8],
    pub name: &'a [u8],
    pub tbl_name: &'a [u8],
    pub rootpage: Record<'a>,
    pub sql: &'a [u8],
}

impl<'a> SQLiteSchema<'a> {
    pub fn from(payload: &'a [u8]) -> anyhow::Result<Self> {
        let mut records = [Record::Null; 5];
        let n = parse_records(payload, &mut records)?;
        if n != 5 {
            anyhow::bail!("sqlite_schema has only {} records", n);
        }
        let _type = if let Record::Text(_type) = records[0] {
            _type
        } else {
            anyhow::bail!("failed to parse type");
        };
        let name = if let Record::Text(name) = records[1] {
            name
        } else {
            anyhow::bail!("failed to parse name");
        };
        let tbl_name = if let Record::Text(tbl_name) = records[2] {
            tbl_name
        } else {
            anyhow::bail!("failed to parse tbl_name");
        };
        let sql = if let Record::Text(sql) = records[4] {
            sql
        } else {
            anyhow::bail!("failed to parse sql");
        };
        Ok(SQLiteSchema {
            _type,
            name,
            tbl_name,
            rootpage: records[3],
            sql,
        })
    }

    pub fn root_page_id(&self) -> anyhow::Result<PageId> {
        Ok(self.rootpage.to_i64()?.try_into()?)
    }
}

#[derive(ThisError, Debug)]
pub enum FindError {
    #[error("table not found")]
    NotFound,
    #[error("{0}")]
    Other(#[from] anyhow::Error),
}

pub fn find_table_page_id<'a>(
    table: &[u8],
    pager: &'a Pager,
    usable_size: u32,
) -> std::result::Result<PageId, FindError> {
    let mut cursor = BtreeCursor::new(ROOT_PAGE_ID, &pager, usable_size)?;
    while let Some(payload) = cursor.next()? {
        if payload.size() == payload.buf().len() as u32 {
            let schema = SQLiteSchema::from(payload.buf())?;
            if schema._type == b"table" && schema.name == table {
                return Ok(schema.root_page_id()?);
            }
        } else if payload.size() <= 10 * 4096 {
            let mut buf = Vec::with_capacity(payload.size() as usize);
            unsafe {
                buf.set_len(payload.size() as usize);
            }
            // SAFETY: buf is not from MemPage.
            let n = unsafe { payload.load(0, &mut buf) }?;
            if n != payload.size() as usize {
                Err(anyhow::anyhow!("failed to load payload: {}", n))?;
            }
            let schema = SQLiteSchema::from(payload.buf())?;
            if schema._type == b"table" && schema.name == table {
                return Ok(schema.root_page_id()?);
            }
        } else {
            Err(anyhow::anyhow!(
                "invalid schema payload size: {}",
                payload.size()
            ))?;
        }
    }
    Err(FindError::NotFound)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;
    use crate::btree::parse_btree_leaf_table_cell;
    use crate::btree::BtreePageHeader;
    use crate::pager::MemPage;
    use crate::pager::PageBuffer;
    use crate::test_utils::*;

    fn load_all_rows<'a>(
        page: &MemPage,
        buffer: &'a PageBuffer<'a>,
        columns: usize,
        usable_size: u32,
    ) -> anyhow::Result<Vec<Vec<Record<'a>>>> {
        let mut result = Vec::new();
        let header = BtreePageHeader::from_page(page, buffer);
        for i in 0..header.n_cells() {
            let (_, _, payload_range, _) =
                parse_btree_leaf_table_cell(&page, &buffer, i, usable_size)
                    .map_err(|e| anyhow::anyhow!("parse btree leaf table cell: {:?}", e))?;
            let payload = &buffer[payload_range];
            // TODO: This is not efficient.
            let mut records = vec![Record::Null; columns];
            // TODO: payload may be multi payload.
            let _ = parse_records(payload, &mut records).unwrap();
            result.push(records);
        }
        Ok(result)
    }

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
    fn parse_sqlite_schema_entry() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let page = pager.get_page(1).unwrap();
        let buffer = page.buffer();
        let usable_size = load_usable_size(file.as_file()).unwrap();
        let (_, _, payload_range, _) =
            parse_btree_leaf_table_cell(&page, &buffer, 0, usable_size).unwrap();
        let payload = &buffer[payload_range];
        let schema = SQLiteSchema::from(payload).unwrap();
        assert_eq!(schema._type, b"table");
        assert_eq!(schema.name, b"example");
        assert_eq!(schema.tbl_name, b"example");
        assert_eq!(schema.root_page_id().unwrap(), 2);
        assert_eq!(schema.sql, b"CREATE TABLE example(col)");
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

    #[test]
    fn test_parse_record() {
        let tables = [
            "CREATE TABLE example(col);",
            "CREATE TABLE example2(col1, col2);",
            "CREATE TABLE example4(col1, col2, col3, col4);",
        ];
        const ONE: i64 = 1;
        let inserts = [
            format!("INSERT INTO example4(col1, col2, col4) VALUES (null, true, false);"),
            format!("INSERT INTO example4(col1, col2, col3, col4) VALUES ({}, {}, {}, {});", i8::MAX, i8::MIN, i16::MAX, i16::MIN),
            format!("INSERT INTO example4(col1, col2, col3, col4) VALUES ({}, {}, {}, {});", (ONE << 23)-1, -(ONE<<23), i32::MAX, i32::MIN),
            format!("INSERT INTO example4(col1, col2, col3, col4) VALUES ({}, {}, {}, {});", (ONE << 47)-1, -(ONE<<47), i64::MAX, i64::MIN),
            format!("INSERT INTO example4(col1, col2, col3, col4) VALUES (0, 1, \"hello\", X'0123456789abcdef');"),
            format!("INSERT INTO example4(col1) VALUES (0.5);"),
        ];
        let mut queries = Vec::new();
        queries.extend(tables);
        queries.extend(inserts.iter().map(|s| s.as_str()));
        let file = create_sqlite_database(&queries);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let usable_size = load_usable_size(file.as_file()).unwrap();
        let page_id = find_table_page_id(b"example4", &pager, usable_size).unwrap();

        let page = pager.get_page(page_id).unwrap();
        let buffer = page.buffer();
        let result: Vec<Vec<Record>> = load_all_rows(&page, &buffer, 4, usable_size).unwrap();

        assert!(matches!(result[0][0], Record::Null));
        assert!(matches!(result[0][1], Record::One));
        assert!(matches!(result[0][2], Record::Null));
        assert!(matches!(result[0][3], Record::Zero));
        assert!(matches!(result[1][0], Record::Int8(_)));
        assert!(matches!(result[1][1], Record::Int8(_)));
        assert!(matches!(result[1][2], Record::Int16(_)));
        assert!(matches!(result[1][3], Record::Int16(_)));
        assert_eq!(result[1][0].to_i64().unwrap(), i8::MAX as i64);
        assert_eq!(result[1][1].to_i64().unwrap(), i8::MIN as i64);
        assert_eq!(result[1][2].to_i64().unwrap(), i16::MAX as i64);
        assert_eq!(result[1][3].to_i64().unwrap(), i16::MIN as i64);
        assert!(matches!(result[2][0], Record::Int24(_)));
        assert!(matches!(result[2][1], Record::Int24(_)));
        assert!(matches!(result[2][2], Record::Int32(_)));
        assert!(matches!(result[2][3], Record::Int32(_)));
        assert_eq!(result[2][0].to_i64().unwrap(), (ONE << 23) - 1);
        assert_eq!(result[2][1].to_i64().unwrap(), -(ONE << 23));
        assert_eq!(result[2][2].to_i64().unwrap(), i32::MAX as i64);
        assert_eq!(result[2][3].to_i64().unwrap(), i32::MIN as i64);
        assert!(matches!(result[3][0], Record::Int48(_)));
        assert!(matches!(result[3][1], Record::Int48(_)));
        assert!(matches!(result[3][2], Record::Int64(_)));
        assert!(matches!(result[3][3], Record::Int64(_)));
        assert_eq!(result[3][0].to_i64().unwrap(), (ONE << 47) - 1);
        assert_eq!(result[3][1].to_i64().unwrap(), -(ONE << 47));
        assert_eq!(result[3][2].to_i64().unwrap(), i64::MAX);
        assert_eq!(result[3][3].to_i64().unwrap(), i64::MIN);
        assert!(matches!(result[4][0], Record::Zero));
        assert!(matches!(result[4][1], Record::One));
        assert!(matches!(result[4][2], Record::Text(_)));
        assert!(matches!(result[4][3], Record::Blob(_)));
        assert_eq!(result[4][0].to_i64().unwrap(), 0);
        assert_eq!(result[4][1].to_i64().unwrap(), 1);
        assert_eq!(result[4][2].to_slice().unwrap(), b"hello");
        assert_eq!(
            result[4][3].to_slice().unwrap(),
            [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef]
        );
        assert!(matches!(result[5][0], Record::Float64(_)));
        assert_eq!(result[5][0].to_f64().unwrap(), 0.5);
    }
}
