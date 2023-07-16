use std::num::NonZeroU32;

use crate::pager::MemPage;
use crate::pager::PageId;
use crate::utils::parse_varint;

type ParseError = &'static str;
type ParseResult<T> = std::result::Result<T, ParseError>;

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

    pub fn from_page(page: &'page MemPage) -> Self {
        // SAFETY: PageBuffer is always more than 512 bytes.
        Self(
            page.buffer[page.header_offset..page.header_offset + BTREE_PAGE_HEADER_MAX_SIZE]
                .try_into()
                .unwrap(),
        )
    }

    /// The btree page type
    ///
    /// TODO: how to convert u8 into enum with zero copy?
    pub fn pagetype(&self) -> &u8 {
        &self.0[0]
    }

    /// Whether the page is a leaf page
    pub fn is_leaf(&self) -> bool {
        self.0[0] & LEAF_FLAG != 0
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

fn get_cell_buffer<'page>(
    page: &MemPage<'page>,
    cell_idx: u16,
    header_size: u8,
) -> ParseResult<&'page [u8]> {
    let cell_pointer_offset = page.header_offset + header_size as usize + (cell_idx << 1) as usize;
    if cell_pointer_offset + 2 > page.buffer.len() {
        return Err("cell pointer out of range");
    }
    let cell_offset = u16::from_be_bytes(
        page.buffer[cell_pointer_offset..cell_pointer_offset + 2]
            .try_into()
            .unwrap(),
    ) as usize;
    if cell_offset > page.buffer.len() {
        return Err("cell offset out of range");
    }
    Ok(&page.buffer[cell_offset..])
}

#[derive(Debug, Clone, Copy)]
pub struct OverflowPage {
    page_id: NonZeroU32,
    remaining_size: i64,
}

impl OverflowPage {
    pub fn page_id(&self) -> PageId {
        self.page_id.get()
    }

    pub fn parse<'a>(&self, page: &MemPage<'a>) -> ParseResult<(&'a [u8], Option<OverflowPage>)> {
        let next_page_id = PageId::from_be_bytes(page.buffer[..4].try_into().unwrap());
        if next_page_id == 0 {
            let tail = 4 + self.remaining_size as usize;
            if page.buffer.len() >= tail {
                Ok((&page.buffer[4..tail], None))
            } else {
                Err("overflow payload does not have next page id")
            }
        } else {
            let payload = &page.buffer[4..];
            let remaining_size = self.remaining_size - payload.len() as i64;
            if remaining_size > 0 {
                Ok((
                    payload,
                    Some(Self {
                        // Safe because it already checks next_page_id != 0.
                        page_id: unsafe { NonZeroU32::new_unchecked(next_page_id) },
                        remaining_size,
                    }),
                ))
            } else {
                Err("overflow page has too many next page")
            }
        }
    }
}

pub struct BtreeLeafTableCell<'page> {
    buf: &'page [u8],
}

impl<'page> BtreeLeafTableCell<'page> {
    pub fn get(page: &MemPage<'page>, cell_idx: u16) -> ParseResult<Self> {
        Ok(Self {
            buf: get_cell_buffer(page, cell_idx, BTREE_PAGE_LEAF_HEADER_SIZE as u8)?,
        })
    }

    pub fn parse(
        &self,
        usable_size: u32,
    ) -> ParseResult<(i64, i64, &'page [u8], Option<OverflowPage>)> {
        let usable_size = usable_size as i64;
        let (payload_length, consumed1) =
            parse_varint(self.buf).map_or(Err("parse payload length varint"), |v| Ok(v))?;
        let (key, consumed2) =
            parse_varint(&self.buf[consumed1..]).map_or(Err("parse key varint"), |v| Ok(v))?;
        let header_length = consumed1 + consumed2;

        let x = usable_size - 35;
        if payload_length <= x {
            if self.buf.len() >= header_length + payload_length as usize {
                Ok((
                    key,
                    payload_length,
                    &self.buf[header_length..header_length + payload_length as usize],
                    None,
                ))
            } else {
                Err("payload length is too large in single cell")
            }
        } else {
            let m = ((usable_size - 12) * 32 / 255) - 23;
            let k = m + ((payload_length - m) % (usable_size - 4));
            let payload_size_in_cell = if k <= x { k } else { m };
            let tail_payload = header_length + payload_size_in_cell as usize;
            if tail_payload + 4 > self.buf.len() {
                return Err("next page id out of range");
            }
            let next_page_id =
                PageId::from_be_bytes(self.buf[tail_payload..tail_payload + 4].try_into().unwrap());
            if next_page_id > 0 {
                Ok((
                    key,
                    payload_length,
                    &self.buf[header_length..tail_payload],
                    Some(OverflowPage {
                        // Safe because next_page_id != 0 is asserted.
                        page_id: unsafe { NonZeroU32::new_unchecked(next_page_id) },
                        remaining_size: payload_length - payload_size_in_cell,
                    }),
                ))
            } else {
                Err("next page id is zero")
            }
        }
    }
}

pub struct BtreeInteriorTableCell<'page> {
    buf: &'page [u8],
}

impl<'page> BtreeInteriorTableCell<'page> {
    pub fn get(page: &MemPage<'page>, cell_idx: u16) -> ParseResult<Self> {
        let buf = get_cell_buffer(page, cell_idx, BTREE_PAGE_INTERIOR_HEADER_SIZE as u8)?;
        if buf.len() < 5 {
            return Err("btree interior table cell buffer is too short");
        }
        Ok(Self { buf })
    }

    pub fn page_id(&self) -> PageId {
        PageId::from_be_bytes(self.buf[..4].try_into().unwrap())
    }

    pub fn key(&self) -> ParseResult<i64> {
        let (key, _) =
            parse_varint(&self.buf[4..]).map_or(Err("parse payload length varint"), |v| Ok(v))?;
        Ok(key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::find_table_page_id;
    use crate::test_utils::*;
    use crate::utils::unsafe_parse_varint;
    use crate::DATABASE_HEADER_SIZE;

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

    #[test]
    fn validate_btree_page_header() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();

        let page1 = pager.get_page(1).unwrap();
        let page1_header = BtreePageHeader::from(
            page1.buffer[DATABASE_HEADER_SIZE..DATABASE_HEADER_SIZE + 12]
                .try_into()
                .unwrap(),
        );
        let page2 = pager.get_page(2).unwrap();
        let page2_header = BtreePageHeader::from(page2.buffer[..12].try_into().unwrap());

        assert_eq!(*page1_header.pagetype(), BTREE_PAGE_TYPE_LEAF_TABLE);
        assert_eq!(*page2_header.pagetype(), BTREE_PAGE_TYPE_LEAF_TABLE);
        assert_eq!(page1_header.n_cells(), 1);
        assert_eq!(page2_header.n_cells(), 0);
    }

    #[test]
    fn load_btree_leaf_table_cell() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let page1 = pager.get_page(1).unwrap();
        let usable_size = load_usable_size(file.as_file()).unwrap();
        let page1_header = BtreePageHeader::from_page(&page1);

        assert_eq!(page1_header.n_cells(), 1);
        let cell = BtreeLeafTableCell::get(&page1, 0).unwrap();

        let (key, size, payload, _) = cell.parse(usable_size).unwrap();
        assert_eq!(key, 1);
        assert_eq!(size, payload.len() as i64);
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
    fn test_overflow_payload() {
        let mut queries = vec!["CREATE TABLE example(col);"];
        let mut buf = Vec::with_capacity(10000);
        for i in 0..10000 {
            buf.push((i % 256) as u8);
        }
        let query = format!(
            "INSERT INTO example(col) VALUES (X'{}');",
            buffer_to_hex(&buf)
        );
        queries.push(&query);
        let file = create_sqlite_database(&queries);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let usable_size = load_usable_size(file.as_file()).unwrap();
        let page_id = find_table_page_id(b"example", &pager, usable_size).unwrap();
        let page = pager.get_page(page_id).unwrap();
        assert_eq!(BtreePageHeader::from_page(&page).n_cells(), 1);

        let cell = BtreeLeafTableCell::get(&page, 0).unwrap();
        let (_, _, mut payload, mut next_payload) = cell.parse(usable_size).unwrap();
        let (header_size, c1) = unsafe_parse_varint(payload);
        let (serial_type, c2) = unsafe_parse_varint(&payload[c1..]);
        let payload_size = (serial_type - 12) / 2;
        assert_eq!(payload_size, buf.len() as i64);
        assert_eq!(header_size, (c1 + c2) as i64);
        payload = &payload[header_size as usize..];
        assert_ne!(payload.len(), buf.len());
        assert_eq!(payload, &buf[..payload.len()]);
        let mut cur = payload.len();
        while cur < buf.len() {
            assert!(next_payload.is_some());
            let page = pager
                .get_page(next_payload.as_ref().unwrap().page_id())
                .unwrap();
            (payload, next_payload) = next_payload.as_ref().unwrap().parse(&page).unwrap();
            assert_eq!(payload, &buf[cur..cur + payload.len()]);
            cur += payload.len();
        }
    }
}
