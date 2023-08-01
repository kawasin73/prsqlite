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

use std::num::NonZeroU32;
use std::ops::Range;

use crate::pager::MemPage;
use crate::pager::PageBuffer;
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

    pub fn from_page(page: &MemPage, buffer: &'page PageBuffer<'page>) -> Self {
        // SAFETY: PageBuffer is always more than 512 bytes.
        Self(
            buffer[page.header_offset..page.header_offset + BTREE_PAGE_HEADER_MAX_SIZE]
                .try_into()
                .unwrap(),
        )
    }

    /// The btree page type
    ///
    /// TODO: how to convert u8 into enum with zero copy?
    pub fn pagetype(&self) -> u8 {
        self.0[0]
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
        let is_interior = (!self.pagetype()) & LEAF_FLAG;
        // 0(leaf) or 4(interior)
        let additional_size = is_interior >> 1;
        8 + additional_size
    }
}

pub struct TableCellKeyParser<'a> {
    page: &'a MemPage,
    buffer: &'a PageBuffer<'a>,
    pub is_leaf: bool,
    header_size: u8,
}

impl<'a> TableCellKeyParser<'a> {
    pub fn new(page: &'a MemPage, buffer: &'a PageBuffer<'a>) -> Self {
        let header = BtreePageHeader::from_page(page, buffer);
        Self {
            page,
            buffer,
            is_leaf: header.is_leaf(),
            header_size: header.header_size(),
        }
    }

    pub fn get_cell_key(&self, cell_idx: u16) -> ParseResult<i64> {
        let offset = get_cell_offset(self.page, self.buffer, cell_idx, self.header_size)?;
        if self.is_leaf {
            // TODO: just skip bytes >= 0x80 because payload length is u32.
            let (_, n) = parse_varint(&self.buffer[offset..]).ok_or("parse payload length varint")?;
            let (key, _) = parse_varint(&self.buffer[offset + n..]).ok_or("parse key varint")?;
            Ok(key)
        } else {
            let (key, _) = parse_varint(&self.buffer[offset + 4..]).ok_or("parse key varint")?;
            Ok(key)
        }
    }
}

fn get_cell_buffer<'page>(
    page: &MemPage,
    buffer: &'page PageBuffer<'page>,
    cell_idx: u16,
    header_size: u8,
) -> ParseResult<&'page [u8]> {
    let cell_pointer_offset = page.header_offset + header_size as usize + (cell_idx << 1) as usize;
    if cell_pointer_offset + 2 > buffer.len() {
        return Err("cell pointer out of range");
    }
    let cell_offset =
        u16::from_be_bytes(buffer[cell_pointer_offset..cell_pointer_offset + 2].try_into().unwrap()) as usize;
    if cell_offset > buffer.len() {
        return Err("cell offset out of range");
    }
    Ok(&buffer[cell_offset..])
}

/// Returns the offset of the cell in the buffer.
///
/// Returned cell offset is in the range of the buffer.
fn get_cell_offset(page: &MemPage, buffer: &[u8], cell_idx: u16, header_size: u8) -> ParseResult<usize> {
    let cell_pointer_offset = page.header_offset + header_size as usize + (cell_idx << 1) as usize;
    if cell_pointer_offset + 2 > buffer.len() {
        return Err("cell pointer out of range");
    }
    let cell_offset =
        u16::from_be_bytes(buffer[cell_pointer_offset..cell_pointer_offset + 2].try_into().unwrap()) as usize;
    if cell_offset > buffer.len() {
        return Err("cell offset out of range");
    }
    Ok(cell_offset)
}

#[derive(Debug, Clone, Copy)]
pub struct OverflowPage {
    page_id: NonZeroU32,
    remaining_size: i32,
}

impl OverflowPage {
    pub fn page_id(&self) -> PageId {
        self.page_id.get()
    }

    pub fn parse<'a>(&self, buffer: &'a PageBuffer<'a>) -> ParseResult<(&'a [u8], Option<OverflowPage>)> {
        let next_page_id = PageId::from_be_bytes(buffer[..4].try_into().unwrap());
        if next_page_id == 0 {
            let tail = 4 + self.remaining_size as usize;
            if buffer.len() >= tail {
                Ok((&buffer[4..tail], None))
            } else {
                Err("overflow payload does not have next page id")
            }
        } else {
            let payload = &buffer[4..];
            if self.remaining_size > payload.len() as i32 {
                Ok((
                    payload,
                    Some(Self {
                        // Safe because it already checks next_page_id != 0.
                        page_id: unsafe { NonZeroU32::new_unchecked(next_page_id) },
                        remaining_size: self.remaining_size - payload.len() as i32,
                    }),
                ))
            } else {
                Err("overflow page has too many next page")
            }
        }
    }
}

pub fn parse_btree_leaf_table_cell(
    page: &MemPage,
    buffer: &[u8],
    cell_idx: u16,
    usable_size: i32,
) -> ParseResult<(i64, i32, Range<usize>, Option<OverflowPage>)> {
    let cell_offset = get_cell_offset(page, buffer, cell_idx, BTREE_PAGE_LEAF_HEADER_SIZE as u8).unwrap();
    let (payload_length, consumed1) =
        parse_varint(&buffer[cell_offset..]).map_or(Err("parse payload length varint"), Ok)?;
    // The maximum payload length is 2147483647 (= i32::MAX).
    let payload_length: i32 = payload_length.try_into().map_err(|_| "payload length too large")?;
    if payload_length < 0 {
        return Err("payload length is negative");
    }
    let (key, consumed2) = parse_varint(&buffer[cell_offset + consumed1..]).map_or(Err("parse key varint"), Ok)?;
    let header_length = consumed1 + consumed2;

    let x = usable_size - 35;
    if payload_length <= x {
        if buffer.len() >= cell_offset + header_length + payload_length as usize {
            Ok((
                key,
                payload_length,
                cell_offset + header_length..cell_offset + header_length + payload_length as usize,
                None,
            ))
        } else {
            Err("payload length is too large in single cell")
        }
    } else {
        let m = ((usable_size - 12) * 32 / 255) - 23;
        let k = m + ((payload_length - m) % (usable_size - 4));
        let payload_size_in_cell = if k <= x { k } else { m };
        let tail_payload = cell_offset + header_length + payload_size_in_cell as usize;
        if tail_payload + 4 > buffer.len() {
            return Err("next page id out of range");
        }
        let next_page_id = PageId::from_be_bytes(buffer[tail_payload..tail_payload + 4].try_into().unwrap());
        if next_page_id > 0 {
            Ok((
                key,
                payload_length,
                cell_offset + header_length..tail_payload,
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

pub struct BtreeInteriorTableCell<'page> {
    buf: &'page [u8],
}

impl<'page> BtreeInteriorTableCell<'page> {
    pub fn get(page: &MemPage, buffer: &'page PageBuffer<'page>, cell_idx: u16) -> ParseResult<Self> {
        let buf = get_cell_buffer(page, buffer, cell_idx, BTREE_PAGE_INTERIOR_HEADER_SIZE as u8)?;
        if buf.len() < 5 {
            return Err("btree interior table cell buffer is too short");
        }
        Ok(Self { buf })
    }

    pub fn page_id(&self) -> PageId {
        PageId::from_be_bytes(self.buf[..4].try_into().unwrap())
    }

    pub fn key(&self) -> ParseResult<i64> {
        let (key, _) = parse_varint(&self.buf[4..]).map_or(Err("parse payload length varint"), Ok)?;
        Ok(key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

            assert_eq!(header.pagetype(), t);
        }
    }

    #[test]
    fn headersize() {
        let mut buf = [0_u8; 12];
        for t in [BTREE_PAGE_TYPE_INTERIOR_INDEX, BTREE_PAGE_TYPE_INTERIOR_TABLE] {
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
        let buffer1 = page1.buffer();
        let page1_header = BtreePageHeader::from(
            buffer1[DATABASE_HEADER_SIZE..DATABASE_HEADER_SIZE + 12]
                .try_into()
                .unwrap(),
        );
        let page2 = pager.get_page(2).unwrap();
        let buffer2 = page2.buffer();
        let page2_header = BtreePageHeader::from(buffer2[..12].try_into().unwrap());

        assert_eq!(page1_header.pagetype(), BTREE_PAGE_TYPE_LEAF_TABLE);
        assert_eq!(page2_header.pagetype(), BTREE_PAGE_TYPE_LEAF_TABLE);
        assert_eq!(page1_header.n_cells(), 1);
        assert_eq!(page2_header.n_cells(), 0);
    }

    #[test]
    fn load_btree_leaf_table_cell() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let page1 = pager.get_page(1).unwrap();
        let buffer1 = page1.buffer();
        let usable_size = load_usable_size(file.as_file()).unwrap();
        let page1_header = BtreePageHeader::from_page(&page1, &buffer1);
        assert_eq!(page1_header.n_cells(), 1);

        let (key, size, payload_range, _) = parse_btree_leaf_table_cell(&page1, &buffer1, 0, usable_size).unwrap();
        let payload = &buffer1[payload_range];
        assert_eq!(key, 1);
        assert_eq!(size as usize, payload.len());
        assert_eq!(
            payload,
            &[
                6, 23, 27, 27, 1, 63, 116, 97, 98, 108, 101, 101, 120, 97, 109, 112, 108, 101, 101, 120, 97, 109, 112,
                108, 101, 2, 67, 82, 69, 65, 84, 69, 32, 84, 65, 66, 76, 69, 32, 101, 120, 97, 109, 112, 108, 101, 40,
                99, 111, 108, 41
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
        let query = format!("INSERT INTO example(col) VALUES (X'{}');", buffer_to_hex(&buf));
        queries.push(&query);
        let file = create_sqlite_database(&queries);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let usable_size = load_usable_size(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());
        let page = pager.get_page(page_id).unwrap();
        let buffer = page.buffer();
        assert_eq!(BtreePageHeader::from_page(&page, &buffer).n_cells(), 1);

        let (_, _, payload_range, mut overflow) = parse_btree_leaf_table_cell(&page, &buffer, 0, usable_size).unwrap();
        let mut payload = &buffer[payload_range];
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
            assert!(overflow.is_some());
            let page = pager.get_page(overflow.as_ref().unwrap().page_id()).unwrap();
            let buffer = page.buffer();
            (payload, overflow) = overflow.as_ref().unwrap().parse(&buffer).unwrap();
            assert_eq!(payload, &buf[cur..cur + payload.len()]);
            cur += payload.len();
        }
    }
}
