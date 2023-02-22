mod btree;
mod utils;

use thiserror::Error;

// TODO: This is to suppress the unused warning.
pub use crate::btree::*;
use crate::utils::parse_varint;

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
}

pub fn parse_record<'a>(headers: &'a [u8], contents: &'a [u8]) -> (Record<'a>, &'a [u8], &'a [u8]) {
    let (serial_type, consumed) = parse_varint(headers);
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

#[derive(Error, Debug)]
pub enum Error {
    #[error("failed to parse: {0}")]
    ParseField(&'static str),
}

pub fn parse_records<'a>(payload: &'a [u8], records: &mut [Record<'a>]) -> anyhow::Result<usize> {
    let (header_size, consumed) = parse_varint(payload);
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
    pub rootpage: &'a [u8],
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
        let rootpage = match records[3] {
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
        let sql = if let Record::Text(sql) = records[4] {
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

pub struct AllRowIterator<'page, 'a> {
    iter: BtreeIterator<'page, 'a>,
    columns: usize,
}

impl<'page> Iterator for AllRowIterator<'page, '_> {
    type Item = Vec<Record<'page>>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(cell) = self.iter.next() {
            let (_, payload) = cell.parse();
            // TODO: This is not efficient.
            let mut records = vec![Record::Null; self.columns];
            let _ = parse_records(payload, &mut records).unwrap();
            Some(records)
        } else {
            None
        }
    }
}

pub fn find_table<'a>(table: &[u8], page1: &'a [u8]) -> anyhow::Result<SQLiteSchema<'a>> {
    let page1 = BtreeLeafTablePage::from(page1, DATABASE_HEADER_SIZE as u8);
    assert_eq!(*page1.header().pagetype(), BTREE_PAGE_TYPE_LEAF_TABLE);
    for cell in page1.iter() {
        let (_, payload) = cell.parse();
        let schema = SQLiteSchema::from(payload)?;
        if schema._type == b"table" && schema.name == table {
            return Ok(schema);
        }
    }
    Err(anyhow::anyhow!("not found"))
}

pub fn load_all_rows<'a>(
    page: &'a BtreeLeafTablePage,
    columns: usize,
) -> anyhow::Result<AllRowIterator<'a, 'a>> {
    Ok(AllRowIterator {
        iter: page.iter(),
        columns,
    })
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
        let page1 = BtreeLeafTablePage::from(&buf[..pagesize], DATABASE_HEADER_SIZE as u8);
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
        let page1 = BtreeLeafTablePage::from(&buf[..pagesize], DATABASE_HEADER_SIZE as u8);
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

    #[test]
    fn find_table_success() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE TABLE example2(col1, col2);",
            "CREATE TABLE example3(col1, col2, col3);",
        ]);
        let buf = fs::read(file.path()).unwrap();
        let header = DatabaseHeader::from(buf[0..DATABASE_HEADER_SIZE].try_into().unwrap());
        let pagesize = header.pagesize() as usize;
        let page1 = &buf[..pagesize];

        let schema = find_table(b"example2", page1).unwrap();
        assert_eq!(schema.name, b"example2");
    }

    #[test]
    fn find_table_not_found() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE TABLE example2(col1, col2);",
            "CREATE TABLE example3(col1, col2, col3);",
        ]);
        let buf = fs::read(file.path()).unwrap();
        let header = DatabaseHeader::from(buf[0..DATABASE_HEADER_SIZE].try_into().unwrap());
        let pagesize = header.pagesize() as usize;
        let page1 = &buf[..pagesize];

        let result = find_table(b"invalid", page1);
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
        let buf = fs::read(file.path()).unwrap();
        let header = DatabaseHeader::from(buf[0..DATABASE_HEADER_SIZE].try_into().unwrap());
        let pagesize = header.pagesize() as usize;
        let page1 = &buf[..pagesize];

        let schema = find_table(b"example4", page1).unwrap();
        let page_id = schema.rootpage[0] as usize;
        let page = BtreeLeafTablePage::from(&buf[(page_id - 1) * pagesize..page_id * pagesize], 0);
        let result: Vec<Vec<Record>> = load_all_rows(&page, 4).unwrap().collect();

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
        println!("result[4][3]: {:?}", result[4][3]);
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
