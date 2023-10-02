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
use crate::pager::PageBufferMut;
use crate::pager::PageId;
use crate::utils::parse_varint;
use crate::utils::u64_to_i64;

type ParseError = &'static str;
type ParseResult<T> = std::result::Result<T, ParseError>;

pub const BTREE_PAGE_INTERIOR_HEADER_SIZE: usize = 12;
pub const BTREE_PAGE_LEAF_HEADER_SIZE: usize = 8;
pub const BTREE_PAGE_HEADER_MAX_SIZE: usize = BTREE_PAGE_INTERIOR_HEADER_SIZE;

const LEAF_FLAG: u8 = 0x08;
const INDEX_FLAG: u8 = 0x02;
const TABLE_FLAG: u8 = 0x05;

pub struct BtreePageType(u8);

impl BtreePageType {
    #[inline]
    pub fn is_leaf(&self) -> bool {
        self.0 & LEAF_FLAG != 0
    }

    #[inline]
    pub fn is_table(&self) -> bool {
        self.0 & TABLE_FLAG != 0
    }

    #[inline]
    pub fn is_index(&self) -> bool {
        self.0 & INDEX_FLAG != 0
    }
}

pub struct BtreePageHeader<'page>(&'page [u8; BTREE_PAGE_HEADER_MAX_SIZE]);

impl<'page> BtreePageHeader<'page> {
    pub fn from_page(page: &MemPage, buffer: &'page PageBuffer<'page>) -> Self {
        // SAFETY: PageBuffer is always more than 512 bytes.
        Self(
            buffer[page.header_offset..page.header_offset + BTREE_PAGE_HEADER_MAX_SIZE]
                .try_into()
                .unwrap(),
        )
    }

    /// The btree page type
    #[inline]
    pub fn page_type(&self) -> BtreePageType {
        BtreePageType(self.0[0])
    }

    /// The offset of the first freeblock, or zero if there are no freeblocks.
    pub fn first_freeblock_offset(&self) -> u16 {
        u16::from_be_bytes(self.0[1..3].try_into().unwrap())
    }

    /// The number of cells in this page
    pub fn n_cells(&self) -> u16 {
        u16::from_be_bytes(self.0[3..5].try_into().unwrap())
    }

    /// The offset of the cell content area
    ///
    /// zero should be interpreted as 65536.
    pub fn cell_content_area_offset(&self) -> u16 {
        u16::from_be_bytes(self.0[5..7].try_into().unwrap())
    }

    /// Fragmented free bytes in the cell content area.
    pub fn fragmented_free_bytes(&self) -> u8 {
        self.0[7]
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
        let is_interior = (!self.0[0]) & LEAF_FLAG;
        // 0(leaf) or 4(interior)
        let additional_size = is_interior >> 1;
        8 + additional_size
    }
}

pub struct BtreePageHeaderMut<'a>(&'a mut [u8; BTREE_PAGE_HEADER_MAX_SIZE]);

impl<'a> BtreePageHeaderMut<'a> {
    pub fn from_page(page: &MemPage, buffer: &'a mut PageBufferMut<'_>) -> Self {
        // SAFETY: PageBuffer is always more than 512 bytes.
        Self(
            (&mut buffer[page.header_offset..page.header_offset + BTREE_PAGE_HEADER_MAX_SIZE])
                .try_into()
                .unwrap(),
        )
    }

    /// Set number of cells in this page
    pub fn set_n_cells(&mut self, n_cells: u16) {
        self.0[3..5].copy_from_slice(n_cells.to_be_bytes().as_slice());
    }

    /// Set offset of the cell content area.
    ///
    /// The offset must be less than 65536. If the actual offset is 65536, it
    /// must be set to 0.
    pub fn set_cell_content_area_offset(&mut self, offset: u16) {
        self.0[5..7].copy_from_slice(offset.to_be_bytes().as_slice());
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
            is_leaf: header.page_type().is_leaf(),
            header_size: header.header_size(),
        }
    }

    pub fn get_cell_key(&self, cell_idx: u16) -> ParseResult<i64> {
        let offset = get_cell_offset(self.page, self.buffer, cell_idx, self.header_size)?;
        let offset_in_cell = if self.is_leaf {
            // TODO: just skip bytes >= 0x80 because payload length is u32.
            let (_, n) =
                parse_varint(&self.buffer[offset..]).ok_or("parse payload length varint")?;
            n
        } else {
            4
        };
        let (key, _) =
            parse_varint(&self.buffer[offset + offset_in_cell..]).ok_or("parse key varint")?;
        Ok(u64_to_i64(key))
    }
}

pub struct IndexCellKeyParser<'a> {
    ctx: &'a BtreeContext,
    page: &'a MemPage,
    buffer: &'a PageBuffer<'a>,
    offset_in_cell: u8,
    header_size: u8,
}

impl<'a> IndexCellKeyParser<'a> {
    pub fn new(ctx: &'a BtreeContext, page: &'a MemPage, buffer: &'a PageBuffer<'a>) -> Self {
        let header = BtreePageHeader::from_page(page, buffer);
        let offset_in_cell = (!header.page_type().is_leaf() as u8) << 2;
        Self {
            ctx,
            page,
            buffer,
            offset_in_cell,
            header_size: header.header_size(),
        }
    }

    pub fn get_cell_key(&self, cell_idx: u16) -> ParseResult<PayloadInfo> {
        let offset = get_cell_offset(self.page, self.buffer, cell_idx, self.header_size)?;
        let offset = offset + self.offset_in_cell as usize;
        let (payload_size, n) =
            parse_varint(&self.buffer[offset..]).ok_or("parse payload length varint")?;
        let payload_size: i32 = payload_size
            .try_into()
            .map_err(|_| "payload length too large")?;
        if payload_size < 0 {
            return Err("payload length is negative");
        }
        PayloadInfo::parse(self.ctx, false, self.buffer, offset + n, payload_size)
    }
}

#[inline]
pub fn cell_pointer_offset(page: &MemPage, cell_idx: u16, header_size: u8) -> usize {
    page.header_offset + header_size as usize + (cell_idx << 1) as usize
}

/// Returns the offset of the cell in the buffer.
///
/// Returned cell offset is in the range of the buffer.
fn get_cell_offset(
    page: &MemPage,
    buffer: &PageBuffer,
    cell_idx: u16,
    header_size: u8,
) -> ParseResult<usize> {
    let cell_pointer_offset = cell_pointer_offset(page, cell_idx, header_size);
    if cell_pointer_offset + 2 > buffer.len() {
        return Err("cell pointer out of range");
    }
    let cell_offset = u16::from_be_bytes(
        buffer[cell_pointer_offset..cell_pointer_offset + 2]
            .try_into()
            .unwrap(),
    ) as usize;
    // offset 0 is used for 65536.
    let cell_offset = if cell_offset == 0 {
        1 << 16
    } else {
        cell_offset
    };
    if cell_offset > buffer.len() {
        return Err("cell offset out of range");
    }
    Ok(cell_offset)
}

/// Context containing constant values to parse btree page.
pub struct BtreeContext {
    /// Maximum local payload size. The first is for index pages, the second is
    /// for table pages.
    max_local: [u16; 2],
    min_local: u16,
    /// Usable size is less than or equal to 65536.
    ///
    /// TODO: Improve the visibility of this field. we may need to re-consider
    /// to merge btree.rs and cursor.rs.
    pub usable_size: u32,
}

impl BtreeContext {
    /// Creates a new context.
    ///
    /// usable_size is at most 65536.
    pub fn new(usable_size: u32) -> Self {
        assert!(usable_size <= 65536);
        Self {
            max_local: [
                (((usable_size - 12) * 64 / 255) - 23).try_into().unwrap(),
                (usable_size - 35).try_into().unwrap(),
            ],
            min_local: ((usable_size - 12) * 32 / 255 - 23).try_into().unwrap(),
            usable_size,
        }
    }

    #[inline]
    fn max_local(&self, is_table: bool) -> u16 {
        self.max_local[is_table as usize]
    }

    #[inline]
    fn n_local(&self, is_table: bool, payload_size: i32) -> u16 {
        let surplus = self.min_local as i32
            + ((payload_size - self.min_local as i32) % (self.usable_size - 4) as i32);
        if surplus <= self.max_local[is_table as usize] as i32 {
            surplus as u16
        } else {
            self.min_local
        }
    }
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

    pub fn parse<'a>(
        &self,
        buffer: &'a PageBuffer<'a>,
    ) -> ParseResult<(&'a [u8], Option<OverflowPage>)> {
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

/// Payload information of a cell.
pub struct PayloadInfo {
    /// The total size of the payload.
    pub payload_size: i32,
    /// The range of the local payload in the page buffer.
    ///
    /// If the size of this range is equal to the payload size, the whole
    /// payload is stored in the local buffer.
    pub local_range: Range<usize>,
    /// The overflow page if the rest of payload is stored in the overflow
    /// pages.
    pub overflow: Option<OverflowPage>,
}

impl PayloadInfo {
    fn parse(
        ctx: &BtreeContext,
        is_table: bool,
        buffer: &PageBuffer,
        offset: usize,
        payload_size: i32,
    ) -> ParseResult<Self> {
        if payload_size <= ctx.max_local(is_table) as i32 {
            if buffer.len() >= offset + payload_size as usize {
                Ok(Self {
                    payload_size,
                    local_range: offset..offset + payload_size as usize,
                    overflow: None,
                })
            } else {
                Err("payload length is too large in single cell")
            }
        } else {
            let payload_size_in_cell = ctx.n_local(is_table, payload_size);
            let tail_payload = offset + payload_size_in_cell as usize;
            if tail_payload + 4 > buffer.len() {
                return Err("next page id out of range");
            }
            let next_page_id =
                PageId::from_be_bytes(buffer[tail_payload..tail_payload + 4].try_into().unwrap());
            if next_page_id > 0 {
                Ok(Self {
                    payload_size,
                    local_range: offset..tail_payload,
                    overflow: Some(OverflowPage {
                        // Safe because next_page_id != 0 is asserted.
                        page_id: unsafe { NonZeroU32::new_unchecked(next_page_id) },
                        remaining_size: payload_size - payload_size_in_cell as i32,
                    }),
                })
            } else {
                Err("next page id is zero")
            }
        }
    }
}

/// Parses a b-tree table leaf page.
pub fn parse_btree_leaf_table_cell(
    ctx: &BtreeContext,
    page: &MemPage,
    buffer: &PageBuffer,
    cell_idx: u16,
) -> ParseResult<(i64, PayloadInfo)> {
    let cell_offset =
        get_cell_offset(page, buffer, cell_idx, BTREE_PAGE_LEAF_HEADER_SIZE as u8).unwrap();
    let (payload_size, consumed1) =
        parse_varint(&buffer[cell_offset..]).map_or(Err("parse payload length varint"), Ok)?;
    // The maximum payload length is 2147483647 (= i32::MAX).
    let payload_size: i32 = payload_size
        .try_into()
        .map_err(|_| "payload length too large")?;
    if payload_size < 0 {
        return Err("payload length is negative");
    }
    let (key, consumed2) =
        parse_varint(&buffer[cell_offset + consumed1..]).map_or(Err("parse key varint"), Ok)?;
    let key = u64_to_i64(key);

    let payload = PayloadInfo::parse(
        ctx,
        /* is_table */ true,
        buffer,
        cell_offset + consumed1 + consumed2,
        payload_size,
    )?;

    Ok((key, payload))
}

/// Parses the page id which a b-tree (table/index) interiror page cell points
/// to.
pub fn parse_btree_interior_cell_page_id(
    page: &MemPage,
    buffer: &PageBuffer,
    cell_idx: u16,
) -> ParseResult<PageId> {
    let cell_offset = get_cell_offset(
        page,
        buffer,
        cell_idx,
        BTREE_PAGE_INTERIOR_HEADER_SIZE as u8,
    )?;
    // Btree interiror cell has 4 bytes page id and at least 1 byte varint (the
    // payload length on index interior page, the key on table interior page).
    if cell_offset + 5 > buffer.len() {
        return Err("btree interior cell buffer is too short");
    }
    let page_id = PageId::from_be_bytes(buffer[cell_offset..cell_offset + 4].try_into().unwrap());
    Ok(page_id)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::*;
    use crate::utils::unsafe_parse_varint;

    const BTREE_PAGE_TYPE_INTERIOR_INDEX: u8 = INDEX_FLAG;
    const BTREE_PAGE_TYPE_INTERIOR_TABLE: u8 = TABLE_FLAG;
    const BTREE_PAGE_TYPE_LEAF_INDEX: u8 = LEAF_FLAG | INDEX_FLAG;
    const BTREE_PAGE_TYPE_LEAF_TABLE: u8 = LEAF_FLAG | TABLE_FLAG;

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

            assert_eq!(header.page_type().0, t);
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
        let buffer1 = page1.buffer();
        let page1_header = BtreePageHeader::from_page(&page1, &buffer1);
        let page2 = pager.get_page(2).unwrap();
        let buffer2 = page2.buffer();
        let page2_header = BtreePageHeader::from_page(&page2, &buffer2);

        assert_eq!(page1_header.page_type().0, BTREE_PAGE_TYPE_LEAF_TABLE);
        assert_eq!(page2_header.page_type().0, BTREE_PAGE_TYPE_LEAF_TABLE);
        assert_eq!(page1_header.n_cells(), 1);
        assert_eq!(page2_header.n_cells(), 0);
    }

    #[test]
    fn test_get_cell_offset() {
        const MAX_PAGESIZE: usize = 1 << 16;
        // page 1 has 0 for cell 0 offset.
        let mut content = [0_u8; 2 * MAX_PAGESIZE];
        let header_size = 12;
        // page 2 has 100 for cell 0 offset.
        content[MAX_PAGESIZE + header_size..MAX_PAGESIZE + header_size + 2]
            .copy_from_slice(&1000_u16.to_be_bytes());
        let pager = create_empty_pager(&content, MAX_PAGESIZE as u32);
        let page = pager.get_page(1).unwrap();
        let buffer = page.buffer();
        // offset 0 is translated to 1 << 16.
        assert_eq!(get_cell_offset(&page, &buffer, 0, 12).unwrap(), 1 << 16);

        let page = pager.get_page(2).unwrap();
        let buffer = page.buffer();
        assert_eq!(get_cell_offset(&page, &buffer, 0, 12).unwrap(), 1000);
    }

    #[test]
    fn test_parse_btree_leaf_table_cell() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let page1 = pager.get_page(1).unwrap();
        let buffer1 = page1.buffer();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page1_header = BtreePageHeader::from_page(&page1, &buffer1);
        assert_eq!(page1_header.n_cells(), 1);

        let (key, payload_info) = parse_btree_leaf_table_cell(&bctx, &page1, &buffer1, 0).unwrap();
        let payload = &buffer1[payload_info.local_range.clone()];
        assert_eq!(key, 1);
        assert_eq!(payload_info.payload_size as usize, payload.len());
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
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());
        let page = pager.get_page(page_id).unwrap();
        let buffer = page.buffer();
        assert_eq!(BtreePageHeader::from_page(&page, &buffer).n_cells(), 1);

        let (_, payload_info) = parse_btree_leaf_table_cell(&bctx, &page, &buffer, 0).unwrap();

        let mut payload = &buffer[payload_info.local_range.clone()];
        let (header_size, c1) = unsafe_parse_varint(payload);
        let (serial_type, c2) = unsafe_parse_varint(&payload[c1..]);
        let payload_size = (serial_type - 12) / 2;
        assert_eq!(payload_size, buf.len() as u64);
        assert_eq!(header_size, (c1 + c2) as u64);
        payload = &payload[header_size as usize..];
        assert_ne!(payload.len(), buf.len());
        assert_eq!(payload, &buf[..payload.len()]);
        let mut cur = payload.len();
        let mut overflow = payload_info.overflow;
        while cur < buf.len() {
            assert!(overflow.is_some());
            let page = pager
                .get_page(overflow.as_ref().unwrap().page_id())
                .unwrap();
            let buffer = page.buffer();
            (payload, overflow) = overflow.as_ref().unwrap().parse(&buffer).unwrap();
            assert_eq!(payload, &buf[cur..cur + payload.len()]);
            cur += payload.len();
        }
    }
}
