use std::num::NonZeroU32;

use crate::pager::PageId;
use crate::utils::parse_varint;

pub const BTREE_PAGE_INTERIOR_HEADER_SIZE: usize = 12;
pub const BTREE_PAGE_LEAF_HEADER_SIZE: usize = 8;
pub const BTREE_PAGE_HEADER_MAX_SIZE: usize = BTREE_PAGE_INTERIOR_HEADER_SIZE;

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

pub struct NextPayload {
    next_page_id: NonZeroU32,
    remaining_size: i64,
}

impl NextPayload {
    pub fn next_page_id(&self) -> PageId {
        self.next_page_id.get()
    }

    pub fn next<'a>(&self, page: &'a [u8]) -> (&'a [u8], Option<NextPayload>) {
        let next_page_id = PageId::from_be_bytes(page[..4].try_into().unwrap());
        if next_page_id == 0 {
            let tail = 4 + self.remaining_size as usize;
            assert!(page.len() >= tail);
            (&page[4..tail], None)
        } else {
            let payload = &page[4..];
            (
                payload,
                Some(Self {
                    // Safe because it already checks next_page_id != 0.
                    next_page_id: unsafe { NonZeroU32::new_unchecked(next_page_id) },
                    remaining_size: self.remaining_size - payload.len() as i64,
                }),
            )
        }
    }
}

pub struct BtreeLeafTableCell<'page> {
    buf: &'page [u8],
}

impl<'page> BtreeLeafTableCell<'page> {
    pub fn parse(&self, usable_size: i64) -> (i64, &'page [u8], Option<NextPayload>) {
        let (payload_length, consumed1) = parse_varint(self.buf);
        let (key, consumed2) = parse_varint(&self.buf[consumed1..]);
        let header_length = consumed1 + consumed2;

        let x = usable_size - 35;
        if payload_length <= x {
            (
                key,
                &self.buf[header_length..header_length + payload_length as usize],
                None,
            )
        } else {
            let m = ((usable_size - 12) * 32 / 255) - 23;
            let k = m + ((payload_length - m) % (usable_size - 4));
            let payload_size_in_cell = if k <= x { k } else { m };
            let tail_payload = header_length + payload_size_in_cell as usize;
            let next_page_id =
                PageId::from_be_bytes(self.buf[tail_payload..tail_payload + 4].try_into().unwrap());
            assert_ne!(next_page_id, 0);
            (
                key,
                &self.buf[header_length..tail_payload],
                Some(NextPayload {
                    // Safe because next_page_id != 0 is asserted.
                    next_page_id: unsafe { NonZeroU32::new_unchecked(next_page_id) },
                    remaining_size: payload_length - payload_size_in_cell,
                }),
            )
        }
    }
}

impl<'page> From<&'page [u8]> for BtreeLeafTableCell<'page> {
    fn from(buf: &'page [u8]) -> Self {
        Self { buf }
    }
}

pub struct BtreeLeafTablePage<'page> {
    page: BtreePage<'page>,
    base_offset: u8,
}

impl<'page> BtreeLeafTablePage<'page> {
    pub fn from(buf: &'page [u8], base_offset: u8) -> Self {
        debug_assert!(buf.len() >= BTREE_PAGE_LEAF_HEADER_SIZE + base_offset as usize);
        Self {
            page: BtreePage::from(buf),
            base_offset,
        }
    }

    pub fn get_cell(&self, i: u16) -> BtreeLeafTableCell<'page> {
        let buf = self
            .page
            .get_cell(i, self.base_offset + BTREE_PAGE_LEAF_HEADER_SIZE as u8);
        BtreeLeafTableCell { buf }
    }

    pub fn header(&'page self) -> BtreePageHeader<'page> {
        self.page.header(self.base_offset)
    }
}

pub struct BtreeInteriorTableCell<'page> {
    buf: &'page [u8],
}

impl<'page> BtreeInteriorTableCell<'page> {
    pub fn parse(&self) -> (&'page [u8; 4], i64) {
        let (key, _) = parse_varint(&self.buf[4..]);
        (self.buf[..4].try_into().unwrap(), key)
    }
}

impl<'page> From<&'page [u8]> for BtreeInteriorTableCell<'page> {
    fn from(buf: &'page [u8]) -> Self {
        Self { buf }
    }
}

pub struct BtreeInteriorTablePage<'page> {
    page: BtreePage<'page>,
    base_offset: u8,
}

impl<'page> BtreeInteriorTablePage<'page> {
    pub fn from(buf: &'page [u8], base_offset: u8) -> Self {
        debug_assert!(buf.len() >= BTREE_PAGE_INTERIOR_HEADER_SIZE + base_offset as usize);
        Self {
            page: BtreePage::from(buf),
            base_offset,
        }
    }

    pub fn get_cell(&self, i: u16) -> BtreeInteriorTableCell<'page> {
        let buf = self
            .page
            .get_cell(i, self.base_offset + BTREE_PAGE_INTERIOR_HEADER_SIZE as u8);
        BtreeInteriorTableCell { buf }
    }

    pub fn header(&'page self) -> BtreePageHeader<'page> {
        self.page.header(self.base_offset)
    }
}

pub struct BtreePage<'page> {
    buf: &'page [u8],
}

impl<'page> BtreePage<'page> {
    pub fn from(buf: &'page [u8]) -> Self {
        Self { buf }
    }

    pub fn get_cell(&self, i: u16, offset: u8) -> &'page [u8] {
        let cell_pointer_offset = offset as usize + (i << 1) as usize;
        let cell_offset = u16::from_be_bytes(
            self.buf[cell_pointer_offset..cell_pointer_offset + 2]
                .try_into()
                .unwrap(),
        ) as usize;
        &self.buf[cell_offset..]
    }

    pub fn header(&'page self, base_offset: u8) -> BtreePageHeader<'page> {
        let base_offset = base_offset as usize;
        BtreePageHeader::from(
            (&self.buf[base_offset..base_offset + BTREE_PAGE_HEADER_MAX_SIZE])
                .try_into()
                .unwrap(),
        )
    }
}

pub struct OverflowPage<'page> {
    buf: &'page [u8],
}

impl<'page> OverflowPage<'page> {
    pub fn next_page_id(&self) -> PageId {
        PageId::from_be_bytes(self.buf[..4].try_into().unwrap())
    }

    pub fn payload(&self) -> &'page [u8] {
        &self.buf[4..]
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
