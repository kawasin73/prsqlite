mod btree;

use thiserror::Error;

// TODO: This is to suppress the unused warning.
pub use crate::btree::*;

pub type PageId = u32;

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

    pub fn pagesize(&self) -> u32 {
        // If the original big endian value is 1, it means 65536.
        (self.0[16] as u32) << 8 | (self.0[17] as u32) << 16
    }

    pub fn reserved(&self) -> &u8 {
        &self.0[20]
    }
}

pub enum Record<'a> {
    Null,
    Int8(&'a [u8; 1]),
    Int16(&'a [u8; 2]),
    Int24(&'a [u8; 3]),
    Int32(&'a [u8; 4]),
    Int48(&'a [u8; 6]),
    Int64(&'a [u8; 8]),
    Float(&'a [u8; 8]),
    Zero,
    One,
    Reserved,
    Blob(&'a [u8]),
    Text(&'a [u8]),
}

pub fn parse_record<'a>(header: &'a [u8], content: &'a [u8]) -> (Record<'a>, &'a [u8], &'a [u8]) {
    assert!(header[0] < 128);
    let serial_size = 1;
    let serial_type = header[0];
    match serial_type {
        0 => (Record::Null, &header[serial_size..], content),
        1 => (
            Record::Int8(content[..1].try_into().unwrap()),
            &header[serial_size..],
            &content[1..],
        ),
        2 => (
            Record::Int16(content[..2].try_into().unwrap()),
            &header[serial_size..],
            &content[2..],
        ),
        3 => (
            Record::Int24(content[..3].try_into().unwrap()),
            &header[serial_size..],
            &content[3..],
        ),
        4 => (
            Record::Int32(content[..4].try_into().unwrap()),
            &header[serial_size..],
            &content[4..],
        ),
        5 => (
            Record::Int48(content[..6].try_into().unwrap()),
            &header[serial_size..],
            &content[6..],
        ),
        6 => (
            Record::Int64(content[..8].try_into().unwrap()),
            &header[serial_size..],
            &content[8..],
        ),
        7 => (
            Record::Float(content[..8].try_into().unwrap()),
            &header[serial_size..],
            &content[8..],
        ),
        8 => (Record::Zero, &header[serial_size..], content),
        9 => (Record::One, &header[serial_size..], content),
        10 | 11 => {
            unimplemented!("reserved record is not implemented");
            // (Record::Reserved,&header[serial_size..],content)
        }
        n if n & 1 == 0 => {
            let size = ((n - 12) >> 1) as usize;
            (
                Record::Blob(&content[..size]),
                &header[serial_size..],
                &content[size..],
            )
        }
        n => {
            let size = ((n - 13) >> 1) as usize;
            (
                Record::Text(&content[..size]),
                &header[serial_size..],
                &content[size..],
            )
        }
    }
}

#[derive(Error, Debug)]
pub enum Error {
    #[error("failed to parse: {0}")]
    ParseField(&'static str),
}
pub struct SQLiteSchema<'a> {
    pub _type: &'a [u8],
    pub name: &'a [u8],
    pub tbl_name: &'a [u8],
    pub rootpage: &'a [u8],
    pub sql: &'a [u8],
}

impl<'a> SQLiteSchema<'a> {
    pub fn from(schema_entry: &'a [u8]) -> anyhow::Result<Self> {
        assert!(schema_entry[0] < 128);
        let header_size = schema_entry[0] as usize;
        let header = &schema_entry[1..header_size];
        let content = &schema_entry[header_size..];
        let (_type, header, content) = parse_record(header, content);
        let (name, header, content) = parse_record(header, content);
        let (tbl_name, header, content) = parse_record(header, content);
        let (rootpage, header, content) = parse_record(header, content);
        let (sql, header, content) = parse_record(header, content);
        if !header.is_empty() {
            anyhow::bail!("failed to parse header");
        }
        if !content.is_empty() {
            anyhow::bail!("failed to parse content");
        }
        let _type = if let Record::Text(_type) = _type {
            _type
        } else {
            anyhow::bail!("failed to parse type");
        };
        let name = if let Record::Text(name) = name {
            name
        } else {
            anyhow::bail!("failed to parse name");
        };
        let tbl_name = if let Record::Text(tbl_name) = tbl_name {
            tbl_name
        } else {
            anyhow::bail!("failed to parse tbl_name");
        };
        let rootpage = match rootpage {
            Record::Int8(v) => v.as_slice(),
            Record::Int16(v) => v.as_slice(),
            Record::Int24(v) => v.as_slice(),
            Record::Int32(v) => v.as_slice(),
            Record::Int48(v) => v.as_slice(),
            Record::Int64(v) => v.as_slice(),
            _ => {
                anyhow::bail!("failed to parse rootpage");
            }
        };
        let sql = if let Record::Text(sql) = sql {
            sql
        } else {
            anyhow::bail!("failed to parse sql");
        };
        Ok(SQLiteSchema {
            _type,
            name,
            tbl_name,
            rootpage,
            sql,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use rusqlite::Connection;
    use tempfile::NamedTempFile;

    use super::*;

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

    fn create_sqlite_database(queries: &[&str]) -> NamedTempFile {
        let file = NamedTempFile::new().unwrap();
        let conn = Connection::open(file.path()).unwrap();
        for query in queries {
            conn.execute(&query, []).unwrap();
        }
        conn.close().unwrap();
        file
    }

    #[test]
    fn validate_database_header() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let buf = fs::read(file.path()).unwrap();

        let header = DatabaseHeader::from(buf[0..DATABASE_HEADER_SIZE].try_into().unwrap());

        assert!(header.validate_magic_header());
        assert_eq!(header.pagesize(), 4096);
        assert!(header.validate_pagesize());
    }

    #[test]
    fn validate_btree_page_header() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let buf = fs::read(file.path()).unwrap();

        let header = DatabaseHeader::from(buf[0..DATABASE_HEADER_SIZE].try_into().unwrap());
        let pagesize = header.pagesize() as usize;
        assert_eq!(buf.len(), 2 * pagesize);
        let page1_header = BtreePageHeader::from(
            buf[DATABASE_HEADER_SIZE..DATABASE_HEADER_SIZE + 12]
                .try_into()
                .unwrap(),
        );
        let page2_header = BtreePageHeader::from(buf[pagesize..pagesize + 12].try_into().unwrap());

        assert_eq!(*page1_header.pagetype(), BTREE_PAGE_TYPE_LEAF_TABLE);
        assert_eq!(*page2_header.pagetype(), BTREE_PAGE_TYPE_LEAF_TABLE);
        assert_eq!(page1_header.n_cells(), 1);
        assert_eq!(page2_header.n_cells(), 0);
    }

    #[test]
    fn load_btree_leaf_table_cell() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let buf = fs::read(file.path()).unwrap();

        let header = DatabaseHeader::from(buf[0..DATABASE_HEADER_SIZE].try_into().unwrap());
        let pagesize = header.pagesize() as usize;
        assert_eq!(buf.len(), 2 * pagesize);

        let page1_header = BtreePageHeader::from(
            buf[DATABASE_HEADER_SIZE..DATABASE_HEADER_SIZE + 12]
                .try_into()
                .unwrap(),
        );
        let page1 = BtreeLeafTablePage::from(&buf[..pagesize]);
        assert_eq!(page1_header.n_cells(), 1);
        let header_size = DATABASE_HEADER_SIZE as u8 + page1_header.header_size();
        let cell = page1.get_cell(0, header_size);

        let (key, payload) = cell.parse();
        assert_eq!(key, 1);
        assert_eq!(
            payload,
            &[
                6, 23, 27, 27, 1, 63, 116, 97, 98, 108, 101, 101, 120, 97, 109, 112, 108, 101, 101,
                120, 97, 109, 112, 108, 101, 2, 67, 82, 69, 65, 84, 69, 32, 84, 65, 66, 76, 69, 32,
                101, 120, 97, 109, 112, 108, 101, 40, 99, 111, 108, 41
            ]
        );
    }

    #[test]
    fn parse_sqlite_schema_entry() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let buf = fs::read(file.path()).unwrap();

        let header = DatabaseHeader::from(buf[0..DATABASE_HEADER_SIZE].try_into().unwrap());
        let pagesize = header.pagesize() as usize;
        let page1_header = BtreePageHeader::from(
            buf[DATABASE_HEADER_SIZE..DATABASE_HEADER_SIZE + 12]
                .try_into()
                .unwrap(),
        );
        let page1 = BtreeLeafTablePage::from(&buf[..pagesize]);
        let header_size = DATABASE_HEADER_SIZE as u8 + page1_header.header_size();
        let cell = page1.get_cell(0, header_size);
        let (_, payload) = cell.parse();
        let schema = SQLiteSchema::from(payload).unwrap();
        assert_eq!(schema._type, b"table");
        assert_eq!(schema.name, b"example");
        assert_eq!(schema.tbl_name, b"example");
        assert_eq!(schema.rootpage, [2]);
        assert_eq!(schema.sql, b"CREATE TABLE example(col)");
    }
}
