use crate::pager::PageId;
use crate::utils::parse_varint;

pub const BTREE_PAGE_HEADER_MAX_SIZE: usize = 12;

const LEAF_FLAG: u8 = 0x08;
const INDEX_FLAG: u8 = 0x02;
const TABLE_FLAG: u8 = 0x05;
pub const BTREE_PAGE_TYPE_INTERIOR_INDEX: u8 = INDEX_FLAG;
pub const BTREE_PAGE_TYPE_INTERIOR_TABLE: u8 = TABLE_FLAG;
pub const BTREE_PAGE_TYPE_LEAF_INDEX: u8 = LEAF_FLAG | INDEX_FLAG;
pub const BTREE_PAGE_TYPE_LEAF_TABLE: u8 = LEAF_FLAG | TABLE_FLAG;

pub struct BtreePageHeader<'page>(&'page [u8; BTREE_PAGE_HEADER_MAX_SIZE]);

impl<'page> BtreePageHeader<'page> {
    pub fn from(buf: &'page [u8; BTREE_PAGE_HEADER_MAX_SIZE]) -> Self {
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

pub struct BtreeLeafTableCell<'page> {
    buf: &'page [u8],
}

impl<'page> BtreeLeafTableCell<'page> {
    pub fn parse(&self) -> (i64, &'page [u8]) {
        let (payload_length, consumed1) = parse_varint(self.buf);
        let (key, consumed2) = parse_varint(&self.buf[consumed1..]);
        let header_length = consumed1 + consumed2;
        // TODO: support multi page payload
        (
            key,
            &self.buf[header_length..header_length + payload_length as usize],
        )
    }
}

pub struct BtreeLeafTablePage<'page> {
    buf: &'page [u8],
    base_offset: u8,
}

impl<'page> BtreeLeafTablePage<'page> {
    pub fn from(buf: &'page [u8], base_offset: u8) -> Self {
        assert!(buf.len() >= BTREE_PAGE_HEADER_MAX_SIZE + base_offset as usize);
        Self { buf, base_offset }
    }

    pub fn get_cell(&self, i: u16, offset: u8) -> BtreeLeafTableCell<'page> {
        let cell_pointer_offset = offset as usize + (i << 1) as usize;
        let cell_offset = u16::from_be_bytes(
            self.buf[cell_pointer_offset..cell_pointer_offset + 2]
                .try_into()
                .unwrap(),
        ) as usize;
        BtreeLeafTableCell {
            buf: &self.buf[cell_offset..],
        }
    }

    pub fn header(&'page self) -> BtreePageHeader<'page> {
        let offset = self.base_offset as usize;
        BtreePageHeader::from(
            (&self.buf[offset..offset + BTREE_PAGE_HEADER_MAX_SIZE])
                .try_into()
                .unwrap(),
        )
    }

    pub fn iter<'a>(&'a self) -> BtreeIterator<'page, 'a> {
        let header = self.header();
        let cells = header.n_cells();
        BtreeIterator {
            page: self,
            cur: 0,
            cells,
            offset: self.base_offset + header.header_size(),
        }
    }
}

pub struct BtreeIterator<'page, 'a> {
    page: &'a BtreeLeafTablePage<'page>,
    cur: u16,
    cells: u16,
    offset: u8,
}

impl<'page> Iterator for BtreeIterator<'page, '_> {
    type Item = BtreeLeafTableCell<'page>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cur < self.cells {
            let cell = self.page.get_cell(self.cur, self.offset);
            self.cur += 1;
            Some(cell)
        } else {
            None
        }
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
