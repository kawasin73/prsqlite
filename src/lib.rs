mod btree;

// TODO: This is to suppress the unused warning.
pub use crate::btree::*;

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
}
