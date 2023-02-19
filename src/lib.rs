const SQLITE_MAX_PAGE_SIZE: usize = 65536;
const DATABASE_HEADER_SIZE: usize = 100;

pub struct DatabaseHeader<'a>(&'a [u8; DATABASE_HEADER_SIZE]);

impl DatabaseHeader<'_> {
    const MAGIC_HEADER: &[u8; 16] = b"SQLite format 3\0";
    pub fn validate_magic_header(&self) -> bool {
        let magic_header: &[u8; 16] = self.0[0..16].try_into().unwrap();
        magic_header == Self::MAGIC_HEADER
    }

    pub fn validate_pagesize(&self) -> bool {
        let pagesize = self.pagesize();
        pagesize >= 512 && pagesize <= SQLITE_MAX_PAGE_SIZE && (pagesize - 1) & pagesize == 0
    }

    pub fn pagesize(&self) -> usize {
        let pagesize = u16::from_be_bytes(self.0[16..18].try_into().unwrap()) as usize;
        if pagesize == 1 {
            SQLITE_MAX_PAGE_SIZE
        } else {
            pagesize
        }
    }

    pub fn reserved(&self) -> &u8 {
        &self.0[20]
    }
}

pub struct BtreePageHeader<'a>(&'a [u8; 12]);

pub const BTREE_PAGE_TYPE_INTERIOR_INDEX: u8 = 2;
pub const BTREE_PAGE_TYPE_INTERIOR_TABLE: u8 = 5;
pub const BTREE_PAGE_TYPE_LEAF_INDEX: u8 = 10;
pub const BTREE_PAGE_TYPE_LEAF_TABLE: u8 = 13;

pub type PageId = u32;

impl BtreePageHeader<'_> {
    /// The btree page type
    ///
    /// TODO: how to convert u8 into enum with zero copy?
    pub fn pagetype(&self) -> &u8 {
        &self.0[0]
    }

    /// The number of cells in this page
    pub fn n_cells(&self) -> u16 {
        u16::from_be_bytes(self.0[3..5].try_into().unwrap())
    }

    /// The right-most pointer
    ///
    /// This is only valid when the page is a interior page.
    pub fn right_page_id(&self) -> PageId {
        u32::from_be_bytes(self.0[8..12].try_into().unwrap())
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use rusqlite::Connection;
    use tempfile::NamedTempFile;

    use super::*;

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

        let header = DatabaseHeader(buf[0..DATABASE_HEADER_SIZE].try_into().unwrap());

        assert!(header.validate_magic_header());
        assert_eq!(header.pagesize(), 4096);
        assert!(header.validate_pagesize());
    }

    #[test]
    fn validate_btree_page_header() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let buf = fs::read(file.path()).unwrap();

        let header = DatabaseHeader(buf[0..DATABASE_HEADER_SIZE].try_into().unwrap());
        let pagesize = header.pagesize();
        assert_eq!(buf.len(), 2 * pagesize);
        let page1_header = BtreePageHeader(
            buf[DATABASE_HEADER_SIZE..DATABASE_HEADER_SIZE + 12]
                .try_into()
                .unwrap(),
        );
        let page2_header = BtreePageHeader(buf[pagesize..pagesize + 12].try_into().unwrap());

        assert_eq!(*page1_header.pagetype(), BTREE_PAGE_TYPE_LEAF_TABLE);
        assert_eq!(*page2_header.pagetype(), BTREE_PAGE_TYPE_LEAF_TABLE);
        assert_eq!(page1_header.n_cells(), 1);
        assert_eq!(page2_header.n_cells(), 0);
    }
}
