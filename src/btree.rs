use crate::PageId;

pub const BTREE_PAGE_HEADER_MAX_SIZE: usize = 12;

const LEAF_FLAG: u8 = 0x08;
const INDEX_FLAG: u8 = 0x02;
const TABLE_FLAG: u8 = 0x05;
pub const BTREE_PAGE_TYPE_INTERIOR_INDEX: u8 = INDEX_FLAG;
pub const BTREE_PAGE_TYPE_INTERIOR_TABLE: u8 = TABLE_FLAG;
pub const BTREE_PAGE_TYPE_LEAF_INDEX: u8 = LEAF_FLAG | INDEX_FLAG;
pub const BTREE_PAGE_TYPE_LEAF_TABLE: u8 = LEAF_FLAG | TABLE_FLAG;

pub struct BtreePageHeader<'a>(&'a [u8; BTREE_PAGE_HEADER_MAX_SIZE]);

impl<'a> BtreePageHeader<'a> {
    pub fn from(buf: &'a [u8; BTREE_PAGE_HEADER_MAX_SIZE]) -> Self {
        Self(buf)
    }

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

    /// The btree page header size.
    ///
    /// * Returns 8 if this is a leaf page.
    /// * Returns 12 if this is an interior page.
    ///
    /// This does not invoke conditional branch.
    pub fn header_size(&self) -> u8 {
        // 0(leaf) or 8(interior)
        let is_interior = (!*self.pagetype()) & LEAF_FLAG;
        // 0(leaf) or 4(interior)
        let additional_size = is_interior >> 1;
        8 + additional_size
    }
}

pub struct BtreeLeafTablePage<'a>(&'a [u8]);

impl<'a> BtreeLeafTablePage<'a> {
    pub fn from(buf: &'a [u8]) -> Self {
        assert!(buf.len() >= BTREE_PAGE_HEADER_MAX_SIZE);
        Self(buf)
    }

    pub fn get_cell(&self, i: u16, header_size: u8) -> BtreeLeafTableCell {
        let cell_pointer_offset = header_size as usize + (i << 1) as usize;
        let cell_offset = u16::from_be_bytes(
            self.0[cell_pointer_offset..cell_pointer_offset + 2]
                .try_into()
                .unwrap(),
        ) as usize;
        BtreeLeafTableCell {
            buf: &self.0[cell_offset..],
        }
    }
}

pub struct BtreeLeafTableCell<'a> {
    buf: &'a [u8],
}

impl BtreeLeafTableCell<'_> {
    pub fn parse(&self) -> (i64, &[u8]) {
        // TODO: support varint
        assert!(self.buf[0] < 128);
        assert!(self.buf[1] < 128);
        (self.buf[1] as i64, &self.buf[2..2 + self.buf[0] as usize])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pagetype() {
        let mut buf = [0_u8; 12];
        for t in [
            BTREE_PAGE_TYPE_INTERIOR_INDEX,
            BTREE_PAGE_TYPE_INTERIOR_TABLE,
            BTREE_PAGE_TYPE_LEAF_INDEX,
            BTREE_PAGE_TYPE_LEAF_TABLE,
        ] {
            buf[0] = t;
            let header = BtreePageHeader(&buf);

            assert_eq!(*header.pagetype(), t);
        }
    }

    #[test]
    fn headersize() {
        let mut buf = [0_u8; 12];
        for t in [
            BTREE_PAGE_TYPE_INTERIOR_INDEX,
            BTREE_PAGE_TYPE_INTERIOR_TABLE,
        ] {
            buf[0] = t;
            let header = BtreePageHeader(&buf);

            assert_eq!(header.header_size(), 12);
        }
        for t in [BTREE_PAGE_TYPE_LEAF_INDEX, BTREE_PAGE_TYPE_LEAF_TABLE] {
            buf[0] = t;
            let header = BtreePageHeader(&buf);

            assert_eq!(header.header_size(), 8);
        }
    }
}
