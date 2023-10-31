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

use std::fmt::Display;
use std::num::NonZeroU32;
use std::ops::Range;

use crate::pager::MemPage;
use crate::pager::PageBuffer;
use crate::pager::PageBufferMut;
use crate::pager::PageId;
use crate::utils::len_varint_buffer;
use crate::utils::parse_varint;
use crate::utils::u64_to_i64;

#[derive(Debug)]
pub struct FileCorrupt(&'static str);

impl std::error::Error for FileCorrupt {}

impl Display for FileCorrupt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("btree corrupt: {}", self.0))
    }
}

type ParseResult<T> = std::result::Result<T, FileCorrupt>;

pub const BTREE_PAGE_INTERIOR_HEADER_SIZE: usize = 12;
pub const BTREE_PAGE_LEAF_HEADER_SIZE: usize = 8;
pub const BTREE_PAGE_HEADER_MAX_SIZE: usize = BTREE_PAGE_INTERIOR_HEADER_SIZE;
pub const BTREE_PAGE_CELL_POINTER_SIZE: usize = 2;

const LEAF_FLAG: u8 = 0x08;
const INDEX_FLAG: u8 = 0x02;
const TABLE_FLAG: u8 = 0x05;

/// Parse 2 bytes big endian value.
///
/// If the value is zero, it is interpreted as 65536.
///
/// This is the same as get2byteNotZero() macro in btree.c of SQLite.
#[inline]
fn parse_non_zero_u16(buf: [u8; 2]) -> NonZeroU32 {
    let v = ((((u16::from_be_bytes(buf) as i32) - 1) & 0xffff) + 1) as u32;
    // TODO: new_unchecked() is safe because v is not zero.
    NonZeroU32::new(v).unwrap()
}

/// TODO: Find non conditional branch way.
pub fn non_zero_to_u16(v: u32) -> u16 {
    if v == 65536 {
        0
    } else {
        v as u16
    }
}

#[inline(always)]
pub fn set_u16(buf: &mut [u8], offset: usize, value: u16) {
    buf[offset..offset + 2].copy_from_slice(&value.to_be_bytes());
}

pub const BTREE_OVERFLOW_PAGE_ID_BYTES: usize = 4;

#[derive(Debug, Clone, Copy)]
pub struct BtreePageType(u8);

impl BtreePageType {
    #[inline]
    pub fn interior_type(&self) -> Self {
        Self(self.0 & !LEAF_FLAG)
    }

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

    /// The btree page header size.
    ///
    /// * Returns 8 if this is a leaf page.
    /// * Returns 12 if this is an interior page.
    ///
    /// This does not invoke conditional branch.
    pub fn header_size(&self) -> u8 {
        // 0(leaf) or 8(interior)
        let is_interior = (!self.0) & LEAF_FLAG;
        // 0(leaf) or 4(interior)
        let additional_size = is_interior >> 1;
        8 + additional_size
    }

    pub fn compute_cell_size_fn(&self) -> fn(&BtreeContext, &[u8], usize) -> ParseResult<u16> {
        if self.is_index() {
            todo!("index cell size");
        }
        if self.is_leaf() {
            compute_table_leaf_cell_size
        } else {
            compute_table_interior_cell_size
        }
    }
}

pub struct BtreePageHeader<'page>(&'page [u8; BTREE_PAGE_HEADER_MAX_SIZE]);

impl<'page> BtreePageHeader<'page> {
    pub fn from_page(page: &MemPage, buffer: &'page PageBuffer<'page>) -> Self {
        // SAFETY: PageBuffer is always more than 512 bytes.
        Self::new(page, buffer)
    }

    /// This is used by tests.
    #[allow(dead_code)]
    pub fn from_page_mut(page: &MemPage, buffer: &'page PageBufferMut<'page>) -> Self {
        // SAFETY: PageBufferMut is always more than 512 bytes.
        Self::new(page, buffer)
    }

    // The buffer must from page and more than 512 bytes.
    #[inline(always)]
    fn new(page: &MemPage, buffer: &'page [u8]) -> Self {
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
    /// zero is interpreted as 65536 in this method.
    pub fn cell_content_area_offset(&self) -> NonZeroU32 {
        parse_non_zero_u16(self.0[5..7].try_into().unwrap())
    }

    /// Fragmented free bytes in the cell content area.
    pub fn fragmented_free_bytes(&self) -> u8 {
        self.0[7]
    }

    /// The right-most pointer
    ///
    /// This is only valid when the page is a interior page.
    pub fn right_page_id(&self) -> ParseResult<PageId> {
        PageId::new(u32::from_be_bytes(self.0[8..12].try_into().unwrap()))
            .ok_or(FileCorrupt("right page id is zero"))
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

    pub fn set_page_type(&mut self, page_type: BtreePageType) {
        self.0[0] = page_type.0;
    }

    /// Set number of cells in this page
    pub fn set_n_cells(&mut self, n_cells: u16) {
        set_u16(self.0, 3, n_cells);
    }

    /// Set offset of the cell content area.
    ///
    /// The offset must be less than 65536. If the actual offset is 65536, it
    /// must be set to 0.
    pub fn set_cell_content_area_offset(&mut self, offset: u16) {
        set_u16(self.0, 5, offset);
    }

    pub fn set_first_freeblock_offset(&mut self, offset: u16) {
        set_u16(self.0, 1, offset);
    }

    pub fn add_fragmented_free_bytes(&mut self, size: u8) {
        self.0[7] += size;
    }

    pub fn clear_fragmented_free_bytes(&mut self) {
        self.0[7] = 0;
    }

    pub fn set_right_page_id(&mut self, page_id: PageId) {
        self.0[8..12].copy_from_slice(&page_id.get().to_be_bytes());
    }
}

pub struct FreeblockIterator<'a> {
    offset: usize,
    buffer: &'a [u8],
}

impl<'a> FreeblockIterator<'a> {
    pub fn new(first_freeblock_offset: u16, buffer: &'a [u8]) -> Self {
        Self {
            offset: first_freeblock_offset as usize,
            buffer,
        }
    }
}

impl<'a> Iterator for FreeblockIterator<'a> {
    type Item = (usize, u16);

    fn next(&mut self) -> Option<Self::Item> {
        if self.offset == 0 {
            None
        } else {
            let offset = self.offset;
            assert!(offset + 4 <= self.buffer.len());
            self.offset =
                u16::from_be_bytes(self.buffer[offset..offset + 2].try_into().unwrap()) as usize;
            let size = u16::from_be_bytes(self.buffer[offset + 2..offset + 4].try_into().unwrap());

            Some((offset, size))
        }
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
        let page_type = BtreePageHeader::from_page(page, buffer).page_type();
        Self {
            page,
            buffer,
            is_leaf: page_type.is_leaf(),
            header_size: page_type.header_size(),
        }
    }

    pub fn get_cell_key(&self, cell_idx: u16) -> ParseResult<i64> {
        let offset = get_cell_offset(self.page, self.buffer, cell_idx, self.header_size)?;
        let offset_in_cell = if self.is_leaf {
            len_varint_buffer(&self.buffer[offset..])
                .ok_or(FileCorrupt("parse payload length varint"))?
        } else {
            4
        };
        let (key, _) = parse_varint(&self.buffer[offset + offset_in_cell..])
            .ok_or(FileCorrupt("parse key varint"))?;
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
        let page_type = BtreePageHeader::from_page(page, buffer).page_type();
        let offset_in_cell = (!page_type.is_leaf() as u8) << 2;
        Self {
            ctx,
            page,
            buffer,
            offset_in_cell,
            header_size: page_type.header_size(),
        }
    }

    pub fn get_cell_key(&self, cell_idx: u16) -> ParseResult<PayloadInfo> {
        let offset = get_cell_offset(self.page, self.buffer, cell_idx, self.header_size)?;
        let offset = offset + self.offset_in_cell as usize;
        let (payload_size, n) = parse_varint(&self.buffer[offset..])
            .ok_or(FileCorrupt("parse payload length varint"))?;
        let payload_size: i32 = payload_size
            .try_into()
            .map_err(|_| FileCorrupt("payload length too large"))?;
        if payload_size < 0 {
            return Err(FileCorrupt("payload length is negative"));
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
pub fn get_cell_offset(
    page: &MemPage,
    // TODO: How to accept both PageBuffer and PageBufferMut?
    buffer: &[u8],
    cell_idx: u16,
    header_size: u8,
) -> ParseResult<usize> {
    let cell_pointer_offset = cell_pointer_offset(page, cell_idx, header_size);
    if cell_pointer_offset + 2 > buffer.len() {
        return Err(FileCorrupt("cell pointer out of range"));
    }
    let cell_offset = parse_non_zero_u16(
        buffer[cell_pointer_offset..cell_pointer_offset + 2]
            .try_into()
            .unwrap(),
    )
    .get() as usize;
    if cell_offset > buffer.len() {
        return Err(FileCorrupt("cell offset out of range"));
    }
    Ok(cell_offset)
}

fn compute_table_leaf_cell_size(
    ctx: &BtreeContext,
    // TODO: How to accept both PageBufferMut and TemporaryPage?
    buffer: &[u8],
    offset: usize,
) -> ParseResult<u16> {
    let (payload_size, payload_size_length) =
        parse_varint(&buffer[offset..]).ok_or(FileCorrupt("parse payload size"))?;
    let key_length = len_varint_buffer(&buffer[offset + payload_size_length..])
        .ok_or(FileCorrupt("key length"))?;
    let n_local = if payload_size <= ctx.max_local(true) as u64 {
        payload_size as u16
    } else {
        ctx.n_local(true, payload_size as i32)
    };
    Ok(payload_size_length as u16 + key_length as u16 + n_local)
}

fn compute_table_interior_cell_size(
    _ctx: &BtreeContext,
    // TODO: How to accept both PageBufferMut and TemporaryPage?
    buffer: &[u8],
    offset: usize,
) -> ParseResult<u16> {
    let key_length = len_varint_buffer(&buffer[offset + 4..]).ok_or(FileCorrupt("key length"))?;
    Ok(4 + key_length as u16)
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
    pub fn max_local(&self, is_table: bool) -> u16 {
        self.max_local[is_table as usize]
    }

    #[inline]
    pub fn n_local(&self, is_table: bool, payload_size: i32) -> u16 {
        assert!(payload_size >= 0);
        let surplus = self.min_local as i32
            + ((payload_size - self.min_local as i32)
                % (self.usable_size - BTREE_OVERFLOW_PAGE_ID_BYTES as u32) as i32);
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
        self.page_id
    }

    pub fn parse<'a>(
        &self,
        ctx: &BtreeContext,
        buffer: &'a PageBuffer<'a>,
    ) -> ParseResult<(&'a [u8], Option<OverflowPage>)> {
        if let Some(next_page_id) = PageId::new(u32::from_be_bytes(
            buffer[..BTREE_OVERFLOW_PAGE_ID_BYTES].try_into().unwrap(),
        )) {
            let payload = &buffer[BTREE_OVERFLOW_PAGE_ID_BYTES..ctx.usable_size as usize];
            if self.remaining_size > payload.len() as i32 {
                Ok((
                    payload,
                    Some(Self {
                        page_id: next_page_id,
                        remaining_size: self.remaining_size - payload.len() as i32,
                    }),
                ))
            } else {
                Err(FileCorrupt("overflow page has too many next page"))
            }
        } else {
            let tail = BTREE_OVERFLOW_PAGE_ID_BYTES + self.remaining_size as usize;
            if buffer.len() >= tail {
                Ok((&buffer[BTREE_OVERFLOW_PAGE_ID_BYTES..tail], None))
            } else {
                Err(FileCorrupt("overflow payload does not have next page id"))
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
                Err(FileCorrupt("payload length is too large in single cell"))
            }
        } else {
            let payload_size_in_cell = ctx.n_local(is_table, payload_size);
            let tail_payload = offset + payload_size_in_cell as usize;
            if tail_payload + BTREE_OVERFLOW_PAGE_ID_BYTES > buffer.len() {
                return Err(FileCorrupt("next page id out of range"));
            }
            if let Some(next_page_id) = PageId::new(u32::from_be_bytes(
                buffer[tail_payload..tail_payload + BTREE_OVERFLOW_PAGE_ID_BYTES]
                    .try_into()
                    .unwrap(),
            )) {
                Ok(Self {
                    payload_size,
                    local_range: offset..tail_payload,
                    overflow: Some(OverflowPage {
                        page_id: next_page_id,
                        remaining_size: payload_size - payload_size_in_cell as i32,
                    }),
                })
            } else {
                Err(FileCorrupt("next page id is zero"))
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
        parse_varint(&buffer[cell_offset..]).ok_or(FileCorrupt("parse payload length varint"))?;
    // The maximum payload length is 2147483647 (= i32::MAX).
    let payload_size: i32 = payload_size
        .try_into()
        .map_err(|_| FileCorrupt("payload length too large"))?;
    if payload_size < 0 {
        return Err(FileCorrupt("payload length is negative"));
    }
    let (key, consumed2) =
        parse_varint(&buffer[cell_offset + consumed1..]).ok_or(FileCorrupt("parse key varint"))?;
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
        return Err(FileCorrupt("btree interior cell buffer is too short"));
    }
    let page_id = PageId::new(u32::from_be_bytes(
        buffer[cell_offset..cell_offset + 4].try_into().unwrap(),
    ))
    .ok_or(FileCorrupt("btree interior cell page id is zero"))?;
    Ok(page_id)
}

/// Find the first freeblock which is larger than or equal to the given size.
///
/// Remove the freeblock from the freeblock list and returns the offset of the
/// space.
///
/// If the freeblock is 4 byte or more larger than the given size, split the
/// freeblock.
///
/// Returns [None] if there is no freeblocks that matches the size.
pub fn allocate_from_freeblocks(
    page: &MemPage,
    buffer: &mut PageBufferMut,
    first_freeblock_offset: u16,
    size: u16,
) -> Option<usize> {
    // first_freeblock_offset in the header is at offset 1.
    let mut previous_freeblock_offset = page.header_offset + 1;
    for (freeblock_offset, freeblock_size) in FreeblockIterator::new(first_freeblock_offset, buffer)
    {
        if freeblock_size >= size {
            let remaining_size = freeblock_size - size;
            let new_freeblock_offset = if remaining_size < 4 {
                BtreePageHeaderMut::from_page(page, buffer)
                    .add_fragmented_free_bytes(remaining_size as u8);

                buffer[freeblock_offset..freeblock_offset + 2]
                    .try_into()
                    .unwrap()
            } else {
                // Split the freeblock.
                let new_freeblock_offset = freeblock_offset + size as usize;
                buffer.copy_within(freeblock_offset..freeblock_offset + 2, new_freeblock_offset);
                buffer[new_freeblock_offset + 2..new_freeblock_offset + 4]
                    .copy_from_slice(&remaining_size.to_be_bytes());

                (new_freeblock_offset as u16).to_be_bytes()
            };
            buffer[previous_freeblock_offset..previous_freeblock_offset + 2]
                .copy_from_slice(&new_freeblock_offset);
            return Some(freeblock_offset);
        }
        previous_freeblock_offset = freeblock_offset;
    }
    None
}

/// Allocate a space for idx-th cell from the unallocated space.
///
/// This also update cell pointer. Even if a cell of idx exists, it is
/// overwritten.
///
/// NOTE: This does not check if the cell is actually fit in the page.
pub fn allocate_from_unallocated_space(
    page: &MemPage,
    buffer: &mut PageBufferMut,
    header_size: u8,
    cell_content_area_offset: usize,
    idx: u16,
    cell_size: u16,
) -> usize {
    let new_cell_content_area_offset = cell_content_area_offset - cell_size as usize;
    let cell_pointer_offset = cell_pointer_offset(page, idx, header_size);
    set_u16(
        buffer,
        cell_pointer_offset,
        new_cell_content_area_offset as u16,
    );
    new_cell_content_area_offset
}

/// Write a table leaf cell to the specified offset.
pub fn write_table_leaf_cell(
    buffer: &mut PageBufferMut,
    offset: usize,
    cell_header: &[u8],
    local_payload: &[u8],
    overflow_page_id: Option<PageId>,
) {
    // Copy payload to the btree page.
    let payload_offset = offset + cell_header.len();
    buffer[offset..payload_offset].copy_from_slice(cell_header);
    let payload_tail_offset = payload_offset + local_payload.len();
    buffer[payload_offset..payload_tail_offset].copy_from_slice(local_payload);
    if let Some(overflow_page_id) = overflow_page_id {
        let overflow_page_id = overflow_page_id.get().to_be_bytes();
        buffer[payload_tail_offset..payload_tail_offset + overflow_page_id.len()]
            .copy_from_slice(&overflow_page_id);
    }
}

/// Compute the free size of the page.
///
/// n_cells is an argument because this is cached in cursor.
pub fn compute_free_size(page: &MemPage, buffer: &PageBufferMut, n_cells: u16) -> ParseResult<u16> {
    let page_header = BtreePageHeader::from_page_mut(page, buffer);
    let header_size = page_header.page_type().header_size();
    let first_freeblock_offset = page_header.first_freeblock_offset();
    let cell_content_area_offset = page_header.cell_content_area_offset().get() as usize;
    let fragmented_free_bytes = page_header.fragmented_free_bytes();
    let unallocated_space_offset = cell_pointer_offset(page, n_cells, header_size);

    if cell_content_area_offset < unallocated_space_offset {
        return Err(FileCorrupt("invalid cell content area offset"));
    }

    // unallocated_size must fit in u16 because cell_content_area_offset is at most
    // 65536 and unallocated_space_offset must be bigger than 0.
    let unallocated_size = (cell_content_area_offset - unallocated_space_offset) as u16;

    let mut free_size = unallocated_size;
    for (freeblock_offset, size) in FreeblockIterator::new(first_freeblock_offset, buffer) {
        if freeblock_offset < cell_content_area_offset {
            return Err(FileCorrupt("invalid freeblock offset"));
        }
        free_size += size;
    }
    free_size += fragmented_free_bytes as u16;

    Ok(free_size)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pager::PAGE_ID_1;
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
        for t in [
            BTREE_PAGE_TYPE_INTERIOR_INDEX,
            BTREE_PAGE_TYPE_INTERIOR_TABLE,
        ] {
            assert_eq!(BtreePageType(t).header_size(), 12);
        }
        for t in [BTREE_PAGE_TYPE_LEAF_INDEX, BTREE_PAGE_TYPE_LEAF_TABLE] {
            assert_eq!(BtreePageType(t).header_size(), 8);
        }
    }

    #[test]
    fn cell_content_area_offset() {
        let mut buf = [0_u8; 12];

        let header = BtreePageHeader(&buf);
        assert_eq!(header.cell_content_area_offset().get(), 65536);

        buf[6] = 100;
        let header = BtreePageHeader(&buf);
        assert_eq!(header.cell_content_area_offset().get(), 100);

        buf[5] = 100;
        let header = BtreePageHeader(&buf);
        assert_eq!(header.cell_content_area_offset().get(), 25700);
    }

    #[test]
    fn test_btree_page_header() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();

        let page1 = pager.get_page(PAGE_ID_1).unwrap();
        let buffer1 = page1.buffer();
        let page1_header = BtreePageHeader::from_page(&page1, &buffer1);
        let page2 = pager.get_page(PageId::new(2).unwrap()).unwrap();
        let buffer2 = page2.buffer();
        let page2_header = BtreePageHeader::from_page(&page2, &buffer2);

        assert_eq!(page1_header.page_type().0, BTREE_PAGE_TYPE_LEAF_TABLE);
        assert_eq!(page2_header.page_type().0, BTREE_PAGE_TYPE_LEAF_TABLE);
        assert_eq!(page1_header.n_cells(), 1);
        assert_eq!(page2_header.n_cells(), 0);
        assert_eq!(page1_header.page_type().header_size(), 8);
        assert_eq!(page2_header.page_type().header_size(), 8);
        assert_eq!(page1_header.cell_content_area_offset().get(), 4043);
        assert_eq!(page2_header.cell_content_area_offset().get(), 4096);
        assert_eq!(page1_header.first_freeblock_offset(), 0);
        assert_eq!(page2_header.first_freeblock_offset(), 0);
        assert_eq!(page1_header.fragmented_free_bytes(), 0);
        assert_eq!(page2_header.fragmented_free_bytes(), 0);
    }

    #[test]
    fn test_btree_page_header_freeblock() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "INSERT INTO example(col) VALUES (1);",
            "INSERT INTO example(col) VALUES (2);",
            "INSERT INTO example(col) VALUES (3);",
            "INSERT INTO example(col) VALUES (4);",
            "DELETE FROM example WHERE col = 1;",
            "DELETE FROM example WHERE col = 3;",
        ]);
        let page_id = find_table_page_id("example", file.path());
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();

        let page = pager.get_page(page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);

        assert_eq!(page_header.first_freeblock_offset(), 4082);
        assert_eq!(page_header.fragmented_free_bytes(), 0);

        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "INSERT INTO example(col) VALUES (2);",
            "INSERT INTO example(col) VALUES (3);",
            "DELETE FROM example WHERE col = 2;",
            "INSERT INTO example(col) VALUES (1);",
        ]);
        let page_id = find_table_page_id("example", file.path());
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();

        let page = pager.get_page(page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);

        assert_eq!(page_header.first_freeblock_offset(), 0);
        assert_eq!(page_header.fragmented_free_bytes(), 1);
    }

    #[test]
    fn test_freeblock_iterator() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "INSERT INTO example(col) VALUES (1);",
            "INSERT INTO example(col) VALUES (2);",
            "INSERT INTO example(col) VALUES (3);",
            "INSERT INTO example(col) VALUES (4);",
            "DELETE FROM example WHERE col = 1;",
            "DELETE FROM example WHERE col = 3;",
        ]);
        let page_id = find_table_page_id("example", file.path());
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();

        let page = pager.get_page(page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);

        let mut iter = FreeblockIterator::new(page_header.first_freeblock_offset(), &buffer);

        assert_eq!(iter.next(), Some((4082, 5)));
        assert_eq!(iter.next(), Some((4092, 4)));
        assert_eq!(iter.next(), None);
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
        let page = pager.get_page(PAGE_ID_1).unwrap();
        let buffer = page.buffer();
        // offset 0 is translated to 1 << 16.
        assert_eq!(get_cell_offset(&page, &buffer, 0, 12).unwrap(), 1 << 16);

        let page = pager.get_page(PageId::new(2).unwrap()).unwrap();
        let buffer = page.buffer();
        assert_eq!(get_cell_offset(&page, &buffer, 0, 12).unwrap(), 1000);
    }

    #[test]
    fn test_parse_btree_leaf_table_cell() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let page1 = pager.get_page(PAGE_ID_1).unwrap();
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
            (payload, overflow) = overflow.as_ref().unwrap().parse(&bctx, &buffer).unwrap();
            assert_eq!(payload, &buf[cur..cur + payload.len()]);
            cur += payload.len();
        }
    }

    #[test]
    fn test_allocate_from_freeblocks() {
        let pager = create_empty_pager(&[], 4096 * 2);

        let (page_id, _) = pager.allocate_page().unwrap();
        assert_eq!(page_id, PAGE_ID_1);
        let (page_id, _) = pager.allocate_page().unwrap();
        assert_eq!(page_id.get(), 2);

        for page_id in [PAGE_ID_1, PageId::new(2).unwrap()] {
            let page = pager.get_page(page_id).unwrap();
            let mut buffer = pager.make_page_mut(&page).unwrap();

            let mut header = BtreePageHeaderMut::from_page(&page, &mut buffer);
            header.set_first_freeblock_offset(1000);
            let freeblocks = vec![(1000, 10), (1020, 10), (1030, 20), (1050, 50)];
            for i in 0..freeblocks.len() {
                let (offset, size) = freeblocks[i];
                let next_offset = if i + 1 < freeblocks.len() {
                    freeblocks[i + 1].0
                } else {
                    0
                };
                // next freeblock offset
                set_u16(&mut buffer, offset, next_offset as u16);
                // freeblock size
                set_u16(&mut buffer, offset + 2, size);
            }

            assert_eq!(
                FreeblockIterator::new(
                    BtreePageHeader::from_page_mut(&page, &buffer).first_freeblock_offset(),
                    &buffer
                )
                .collect::<Vec<_>>(),
                freeblocks
            );

            assert!(allocate_from_freeblocks(&page, &mut buffer, 1000, 51).is_none());
            assert_eq!(
                allocate_from_freeblocks(&page, &mut buffer, 1000, 25).unwrap(),
                1050
            );

            let page_header = BtreePageHeader::from_page_mut(&page, &buffer);
            assert_eq!(
                FreeblockIterator::new(page_header.first_freeblock_offset(), &buffer)
                    .collect::<Vec<_>>(),
                vec![(1000, 10), (1020, 10), (1030, 20), (1075, 25)]
            );
            assert_eq!(page_header.fragmented_free_bytes(), 0);

            assert_eq!(
                allocate_from_freeblocks(&page, &mut buffer, 1000, 25).unwrap(),
                1075
            );

            let page_header = BtreePageHeader::from_page_mut(&page, &buffer);
            assert_eq!(
                FreeblockIterator::new(page_header.first_freeblock_offset(), &buffer)
                    .collect::<Vec<_>>(),
                vec![(1000, 10), (1020, 10), (1030, 20)]
            );
            assert_eq!(page_header.fragmented_free_bytes(), 0);

            assert_eq!(
                allocate_from_freeblocks(&page, &mut buffer, 1000, 6).unwrap(),
                1000
            );

            let page_header = BtreePageHeader::from_page_mut(&page, &buffer);
            assert_eq!(page_header.first_freeblock_offset(), 1006);
            assert_eq!(
                FreeblockIterator::new(page_header.first_freeblock_offset(), &buffer)
                    .collect::<Vec<_>>(),
                vec![(1006, 4), (1020, 10), (1030, 20)]
            );
            assert_eq!(page_header.fragmented_free_bytes(), 0);

            assert_eq!(
                allocate_from_freeblocks(&page, &mut buffer, 1006, 7).unwrap(),
                1020
            );

            let page_header = BtreePageHeader::from_page_mut(&page, &buffer);
            assert_eq!(
                FreeblockIterator::new(page_header.first_freeblock_offset(), &buffer)
                    .collect::<Vec<_>>(),
                vec![(1006, 4), (1030, 20)]
            );
            assert_eq!(page_header.fragmented_free_bytes(), 3);
        }
    }

    #[test]
    fn test_allocate_from_unallocated_space() {
        let pager = create_empty_pager(&[], 2 * 4096);
        let page_type = BtreePageType(BTREE_PAGE_TYPE_LEAF_TABLE);
        let header_size = page_type.header_size();

        // Tests for page 1.
        let (page_id, page) = pager.allocate_page().unwrap();
        assert_eq!(page_id, PAGE_ID_1);
        let mut buffer = pager.make_page_mut(&page).unwrap();
        let offset = allocate_from_unallocated_space(&page, &mut buffer, header_size, 4096, 0, 100);
        buffer[offset..offset + 100].copy_from_slice(&[1; 100]);
        let offset =
            allocate_from_unallocated_space(&page, &mut buffer, header_size, offset, 2, 200);
        buffer[offset..offset + 200].copy_from_slice(&[3; 200]);
        let offset =
            allocate_from_unallocated_space(&page, &mut buffer, header_size, offset, 1, 300);
        buffer[offset..offset + 300].copy_from_slice(&[2; 300]);
        assert_eq!(offset, 4096 - 600);
        assert_eq!(
            get_cell_offset(&page, &buffer, 0, header_size).unwrap(),
            3996
        );
        assert_eq!(&buffer[3996..4096], &[1; 100]);
        assert_eq!(
            get_cell_offset(&page, &buffer, 2, header_size).unwrap(),
            3796
        );
        assert_eq!(&buffer[3796..3996], &[3; 200]);
        assert_eq!(
            get_cell_offset(&page, &buffer, 1, header_size).unwrap(),
            3496
        );
        assert_eq!(&buffer[3496..3796], &[2; 300]);

        // Test for page non-one.
        let (page_id, page) = pager.allocate_page().unwrap();
        assert_ne!(page_id, PAGE_ID_1);
        let mut buffer = pager.make_page_mut(&page).unwrap();
        let offset = allocate_from_unallocated_space(&page, &mut buffer, header_size, 3000, 0, 100);
        buffer[offset..offset + 100].copy_from_slice(&[1; 100]);
        let offset =
            allocate_from_unallocated_space(&page, &mut buffer, header_size, offset, 2, 200);
        buffer[offset..offset + 200].copy_from_slice(&[3; 200]);
        let offset =
            allocate_from_unallocated_space(&page, &mut buffer, header_size, offset, 1, 300);
        buffer[offset..offset + 300].copy_from_slice(&[2; 300]);
        assert_eq!(offset, 3000 - 600);
        assert_eq!(
            get_cell_offset(&page, &buffer, 0, header_size).unwrap(),
            2900
        );
        assert_eq!(&buffer[2900..3000], &[1; 100]);
        assert_eq!(
            get_cell_offset(&page, &buffer, 2, header_size).unwrap(),
            2700
        );
        assert_eq!(&buffer[2700..2900], &[3; 200]);
        assert_eq!(
            get_cell_offset(&page, &buffer, 1, header_size).unwrap(),
            2400
        );
        assert_eq!(&buffer[2400..2700], &[2; 300]);
    }

    #[test]
    fn test_compute_free_size() {
        let pager = create_empty_pager(&[], 2 * 4096);
        let page_type = BtreePageType(BTREE_PAGE_TYPE_LEAF_TABLE);

        let (page_id, page) = pager.allocate_page().unwrap();
        assert_eq!(page_id, PAGE_ID_1);
        let mut buffer = pager.make_page_mut(&page).unwrap();
        let mut page_header = BtreePageHeaderMut::from_page(&page, &mut buffer);
        page_header.set_page_type(page_type);
        page_header.set_cell_content_area_offset(4096);
        page_header.set_first_freeblock_offset(0);
        page_header.clear_fragmented_free_bytes();
        assert_eq!(compute_free_size(&page, &buffer, 0).unwrap(), 3988);

        let mut page_header = BtreePageHeaderMut::from_page(&page, &mut buffer);
        page_header.set_cell_content_area_offset(4000);
        page_header.add_fragmented_free_bytes(3);
        assert_eq!(compute_free_size(&page, &buffer, 0).unwrap(), 3895);
        assert_eq!(compute_free_size(&page, &buffer, 10).unwrap(), 3875);

        let mut page_header = BtreePageHeaderMut::from_page(&page, &mut buffer);
        page_header.set_cell_content_area_offset(2000);
        page_header.set_first_freeblock_offset(3000);
        // freeblock 3000 ~ 3010
        set_u16(&mut buffer, 3000, 3100);
        set_u16(&mut buffer, 3002, 10);
        // freeblock 3100 ~ 3200
        set_u16(&mut buffer, 3100, 0);
        set_u16(&mut buffer, 3102, 100);
        assert_eq!(compute_free_size(&page, &buffer, 10).unwrap(), 1985);

        let (page_id, page) = pager.allocate_page().unwrap();
        assert_ne!(page_id, PAGE_ID_1);
        let mut buffer = pager.make_page_mut(&page).unwrap();
        let mut page_header = BtreePageHeaderMut::from_page(&page, &mut buffer);
        page_header.set_page_type(page_type);
        page_header.set_cell_content_area_offset(4096);
        page_header.set_first_freeblock_offset(0);
        page_header.clear_fragmented_free_bytes();
        assert_eq!(compute_free_size(&page, &buffer, 0).unwrap(), 4088);

        let mut page_header = BtreePageHeaderMut::from_page(&page, &mut buffer);
        page_header.set_cell_content_area_offset(4000);
        page_header.add_fragmented_free_bytes(3);
        assert_eq!(compute_free_size(&page, &buffer, 0).unwrap(), 3995);
        assert_eq!(compute_free_size(&page, &buffer, 10).unwrap(), 3975);

        let mut page_header = BtreePageHeaderMut::from_page(&page, &mut buffer);
        page_header.set_cell_content_area_offset(2000);
        page_header.set_first_freeblock_offset(3000);
        // freeblock 3000 ~ 3010
        set_u16(&mut buffer, 3000, 3100);
        set_u16(&mut buffer, 3002, 10);
        // freeblock 3100 ~ 3200
        set_u16(&mut buffer, 3100, 0);
        set_u16(&mut buffer, 3102, 100);
        assert_eq!(compute_free_size(&page, &buffer, 10).unwrap(), 2085);
    }
}
