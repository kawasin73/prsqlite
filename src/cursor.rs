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

use std::cmp::Ordering;

use anyhow::bail;

use crate::btree::cell_pointer_offset;
use crate::btree::parse_btree_interior_cell_page_id;
use crate::btree::parse_btree_leaf_table_cell;
use crate::btree::BtreeContext;
use crate::btree::BtreePageHeader;
use crate::btree::BtreePageHeaderMut;
use crate::btree::BtreePageType;
use crate::btree::IndexCellKeyParser;
use crate::btree::PayloadInfo;
use crate::btree::TableCellKeyParser;
use crate::btree::BTREE_OVERFLOW_PAGE_ID_BYTES;
use crate::pager::MemPage;
use crate::pager::PageBuffer;
use crate::pager::PageId;
use crate::pager::Pager;
use crate::record::compare_record;
use crate::utils::i64_to_u64;
use crate::utils::put_varint;
use crate::value::ValueCmp;

pub struct BtreePayload<'a> {
    pager: &'a Pager,
    bctx: &'a BtreeContext,
    local_payload_buffer: PageBuffer<'a>,
    payload_info: PayloadInfo,
}

impl<'a> BtreePayload<'a> {
    /// The size of the payload.
    pub fn size(&self) -> i32 {
        self.payload_info.payload_size
    }

    /// The local payload.
    ///
    /// This may not be the entire payload if there is overflow page.
    pub fn buf(&self) -> &[u8] {
        &self.local_payload_buffer[self.payload_info.local_range.clone()]
    }

    /// Load the payload into the buffer.
    ///
    /// Returns the number of bytes loaded.
    ///
    /// The offset must be less than the size of the payload.
    pub fn load(&self, offset: i32, buf: &mut [u8]) -> anyhow::Result<usize> {
        if offset < 0 {
            bail!("offset must be non-negative");
        } else if offset >= self.payload_info.payload_size {
            bail!("offset exceeds payload size");
        }
        let mut n_loaded = 0;
        let mut offset = offset;
        let mut buf = buf;
        let payload = &self.local_payload_buffer[self.payload_info.local_range.clone()];

        if offset < payload.len() as i32 {
            let local_offset = offset as usize;
            let n = std::cmp::min(payload.len() - local_offset, buf.len());
            // TODO: std::ptr::copy_nonoverlapping
            buf[..n].copy_from_slice(&payload[local_offset..local_offset + n]);
            n_loaded += n;
            offset += n as i32;
            buf = &mut buf[n..];
        }

        let mut cur = payload.len() as i32;
        let mut overflow = self.payload_info.overflow;
        while !buf.is_empty() && cur < self.payload_info.payload_size {
            let overflow_page =
                overflow.ok_or_else(|| anyhow::anyhow!("overflow page is not found"))?;
            let page = self.pager.get_page(overflow_page.page_id())?;
            let buffer = page.buffer();
            let (payload, next_overflow) = overflow_page
                .parse(self.bctx, &buffer)
                .map_err(|e| anyhow::anyhow!("parse overflow: {:?}", e))?;
            if offset < cur + payload.len() as i32 {
                let local_offset = (offset - cur) as usize;
                let n = std::cmp::min(payload.len() - local_offset, buf.len());
                // TODO: std::ptr::copy_nonoverlapping
                buf[..n].copy_from_slice(&payload[local_offset..local_offset + n]);
                n_loaded += n;
                offset += n as i32;
                buf = &mut buf[n..];
            }
            cur += payload.len() as i32;
            overflow = next_overflow;
        }

        Ok(n_loaded)
    }
}

struct CursorPage {
    mem: MemPage,
    idx_cell: u16,
    n_cells: u16,
    page_type: BtreePageType,
    is_leaf: bool,
}

impl CursorPage {
    fn new(mem: MemPage) -> Self {
        let buffer = mem.buffer();
        let page_header = BtreePageHeader::from_page(&mem, &buffer);
        let n_cells = page_header.n_cells();
        let page_type = page_header.page_type();
        let is_leaf = page_type.is_leaf();
        drop(buffer);
        Self {
            mem,
            idx_cell: 0,
            n_cells,
            page_type,
            is_leaf,
        }
    }
}

/// The cursor of btree.
///
/// [BtreeCursor::insert()] may fail to get a writable buffer from the pager if
/// there are another [BtreeCursor] pointing the same btree simultaniously.
pub struct BtreeCursor<'a> {
    pager: &'a Pager,
    btree_ctx: &'a BtreeContext,
    current_page: CursorPage,
    parent_pages: Vec<CursorPage>,
    initialized: bool,
}

impl<'a> BtreeCursor<'a> {
    pub fn new(
        root_page_id: PageId,
        pager: &'a Pager,
        btree_ctx: &'a BtreeContext,
    ) -> anyhow::Result<Self> {
        let mem = pager.get_page(root_page_id)?;
        let page = CursorPage::new(mem);
        Ok(Self {
            pager,
            btree_ctx,
            current_page: page,
            parent_pages: Vec::new(),
            initialized: false,
        })
    }

    /// Move to the specified btree table cell with the key.
    ///
    /// If it does not exist, move to the next cell.
    ///
    /// Returns the key of the cell which cursor is pointing.
    pub fn table_move_to(&mut self, key: i64) -> anyhow::Result<Option<i64>> {
        // TODO: optimize for sequential access. i.e. key == previouse key + 1
        self.move_to_root()?;
        loop {
            if !self.current_page.page_type.is_table() {
                bail!("not a table page");
            }
            let mut i_min = 0;
            let mut i_max = self.current_page.n_cells as usize;
            let buffer = self.current_page.mem.buffer();
            let cell_key_parser = TableCellKeyParser::new(&self.current_page.mem, &buffer);

            let mut max_cell_key = None;
            while i_min < i_max {
                let i_mid = (i_min + i_max) / 2;
                let cell_key = cell_key_parser
                    .get_cell_key(i_mid as u16)
                    .map_err(|e| anyhow::anyhow!("parse table cell key: {:?}", e))?;
                match key.cmp(&cell_key) {
                    Ordering::Less => {
                        i_max = i_mid;
                        max_cell_key = Some(cell_key);
                    }
                    Ordering::Equal => {
                        i_min = i_mid;
                        max_cell_key = Some(cell_key);
                        break;
                    }
                    Ordering::Greater => {
                        i_min = i_mid + 1;
                    }
                }
            }
            self.current_page.idx_cell = i_min as u16;
            if self.current_page.is_leaf {
                self.initialized = true;
                return Ok(max_cell_key);
            }

            let next_page_id = if i_min == self.current_page.n_cells as usize {
                let page_header = BtreePageHeader::from_page(&self.current_page.mem, &buffer);
                page_header.right_page_id()
            } else {
                parse_btree_interior_cell_page_id(
                    &self.current_page.mem,
                    &buffer,
                    self.current_page.idx_cell,
                )
                .map_err(|e| anyhow::anyhow!("get btree interior cell page id: {:?}", e))?
            };
            drop(buffer);
            self.move_to_child(next_page_id)?;
        }
    }

    /// Move to the specified btree index cell with the key.
    ///
    /// If it does not exist, move to the next cell.
    pub fn index_move_to(&mut self, keys: &[ValueCmp]) -> anyhow::Result<()> {
        self.move_to_root()?;
        loop {
            if !self.current_page.page_type.is_index() {
                bail!("not an index page");
            }
            let mut i_min = 0;
            let mut i_max = self.current_page.n_cells as usize;
            let buffer = self.current_page.mem.buffer();
            let cell_key_parser =
                IndexCellKeyParser::new(self.btree_ctx, &self.current_page.mem, &buffer);

            while i_min < i_max {
                let i_mid = (i_min + i_max) / 2;
                let payload_info = cell_key_parser
                    .get_cell_key(i_mid as u16)
                    .map_err(|e| anyhow::anyhow!("parse index cell key: {:?}", e))?;
                let key_payload = BtreePayload {
                    pager: self.pager,
                    bctx: self.btree_ctx,
                    local_payload_buffer: self.current_page.mem.buffer(),
                    payload_info,
                };
                match compare_record(keys, &key_payload)? {
                    Ordering::Less => {
                        i_max = i_mid;
                    }
                    Ordering::Equal => {
                        self.current_page.idx_cell = i_mid as u16;
                        self.initialized = true;
                        return Ok(());
                    }
                    Ordering::Greater => {
                        i_min = i_mid + 1;
                    }
                }
            }
            self.current_page.idx_cell = i_min as u16;
            if self.current_page.is_leaf {
                drop(buffer);
                // If the key is between the last key of the index leaf page and the parent key,
                // we need to adjust the cursor to parent cell.
                if self.current_page.idx_cell == self.current_page.n_cells {
                    loop {
                        if self.back_to_parent()? {
                            if self.current_page.idx_cell == self.current_page.n_cells {
                                continue;
                            }
                        } else {
                            // traversing completed.
                            self.current_page.idx_cell += 1;
                        }
                        break;
                    }
                }
                self.initialized = true;
                return Ok(());
            }

            let next_page_id = if i_min == self.current_page.n_cells as usize {
                let page_header = BtreePageHeader::from_page(&self.current_page.mem, &buffer);
                page_header.right_page_id()
            } else {
                parse_btree_interior_cell_page_id(
                    &self.current_page.mem,
                    &buffer,
                    self.current_page.idx_cell,
                )
                .map_err(|e| anyhow::anyhow!("get btree interior cell page id: {:?}", e))?
            };
            drop(buffer);
            self.move_to_child(next_page_id)?;
        }
    }

    pub fn move_to_first(&mut self) -> anyhow::Result<()> {
        self.move_to_root()?;
        self.current_page.idx_cell = 0;
        if !self.current_page.is_leaf {
            self.move_to_left_most()?;
        }
        self.initialized = true;
        Ok(())
    }

    pub fn move_to_last(&mut self) -> anyhow::Result<()> {
        self.move_to_root()?;
        if self.current_page.n_cells == 0 {
            self.current_page.idx_cell = 0;
        } else {
            while !self.current_page.is_leaf {
                let buffer = self.current_page.mem.buffer();
                let page_header = BtreePageHeader::from_page(&self.current_page.mem, &buffer);
                let page_id = page_header.right_page_id();
                drop(buffer);
                self.move_to_child(page_id)?;
            }
            self.current_page.idx_cell = self.current_page.n_cells - 1;
        }
        self.initialized = true;
        Ok(())
    }

    pub fn move_next(&mut self) -> anyhow::Result<()> {
        if !self.initialized {
            bail!("cursor is not initialized");
        } else if self.parent_pages.is_empty()
            && (self.current_page.idx_cell == self.current_page.n_cells + 1
                || self.current_page.n_cells == 0)
        {
            // The cursor is completed.
            return Ok(());
        }

        self.current_page.idx_cell += 1;
        if self.current_page.is_leaf && self.current_page.idx_cell < self.current_page.n_cells {
            return Ok(());
        }

        if self.current_page.page_type.is_table() {
            // table page never stops in the middle of the interior page.
            assert!(self.current_page.is_leaf);
            assert!(self.current_page.idx_cell == self.current_page.n_cells);
            loop {
                if !self.back_to_parent()? {
                    // traversing completed.
                    self.current_page.idx_cell += 1;
                    break;
                }
                self.current_page.idx_cell += 1;
                if self.move_to_left_most()? {
                    break;
                }
            }
        } else if self.current_page.page_type.is_index() {
            if !self.current_page.is_leaf && self.current_page.idx_cell <= self.current_page.n_cells
            {
                assert!(self.move_to_left_most()?);
            } else {
                assert!(
                    self.current_page.is_leaf
                        && self.current_page.idx_cell == self.current_page.n_cells
                );
                loop {
                    if self.back_to_parent()? {
                        if self.current_page.idx_cell == self.current_page.n_cells {
                            continue;
                        }
                    } else {
                        // traversing completed.
                        self.current_page.idx_cell += 1;
                    }
                    break;
                }
            }
        } else {
            bail!("not a btree page");
        }
        Ok(())
    }

    /// Insert or update a new item to the table.
    ///
    /// There should not be other [BtreeCursor]s pointing the same btree.
    /// Otherwise, this fails.
    pub fn insert(&mut self, key: i64, payload: &[u8]) -> anyhow::Result<()> {
        let current_cell_key = self.table_move_to(key)?;

        let mut cell_header = [0; 18];
        let payload_size: i32 = payload.len().try_into()?;
        let mut cell_header_size = put_varint(cell_header.as_mut_slice(), payload_size as u64);
        cell_header_size += put_varint(&mut cell_header[cell_header_size..], i64_to_u64(key));
        let is_table = true;
        let (cell_size, n_local, overflow_page_id) = if payload_size
            <= self.btree_ctx.max_local(is_table) as i32
        {
            (
                cell_header_size + payload_size as usize,
                payload_size as usize,
                None,
            )
        } else {
            // Split the payload into local and overflow pages.
            let n_local = self.btree_ctx.n_local(is_table, payload_size) as usize;
            let mut i_overflow_payload = n_local;
            let usable_size_overflow =
                self.btree_ctx.usable_size as usize - BTREE_OVERFLOW_PAGE_ID_BYTES;
            let (first_overflow_page_id, mut page) = self.pager.allocate_page()?;
            while i_overflow_payload + usable_size_overflow < payload.len() {
                let (next_page_id, next_page) = self.pager.allocate_page()?;
                let mut buffer = self.pager.make_page_mut(&page)?;
                let next_page_id = next_page_id.to_be_bytes();
                assert_eq!(next_page_id.len(), BTREE_OVERFLOW_PAGE_ID_BYTES);
                buffer[..next_page_id.len()].copy_from_slice(&next_page_id);
                buffer[next_page_id.len()..self.btree_ctx.usable_size as usize].copy_from_slice(
                    &payload[i_overflow_payload..i_overflow_payload + usable_size_overflow],
                );
                drop(buffer);
                i_overflow_payload += usable_size_overflow;
                page = next_page;
            }
            let mut buffer = self.pager.make_page_mut(&page)?;
            let last_overflow_size = payload.len() - i_overflow_payload;
            buffer[..BTREE_OVERFLOW_PAGE_ID_BYTES].fill(0);
            buffer[BTREE_OVERFLOW_PAGE_ID_BYTES..BTREE_OVERFLOW_PAGE_ID_BYTES + last_overflow_size]
                .copy_from_slice(&payload[i_overflow_payload..]);
            drop(buffer);

            (
                cell_header_size + n_local + BTREE_OVERFLOW_PAGE_ID_BYTES,
                n_local,
                Some(first_overflow_page_id.to_be_bytes()),
            )
        };
        // Allocate 4 bytes or more to be compatible to allocateSpace() of SQLite.
        // Otherwise freeSpace() of SQLite corrupts the database file (e.g. on updating
        // or deleting records). 4 bytes allocation is introduced in order to make
        // spaces easier to reused as freeblock. 1 ~ 3 bytes spaces are counted as
        // fragmented and never reused. cell_size can be less than 4 on index pages.
        let cell_size = if cell_size < 4 { 4 } else { cell_size };

        // TODO: split the payload into overflow page if it is too large.

        match current_cell_key {
            Some(current_cell_key) if current_cell_key == key => {
                // TODO: Update the payload
                todo!("update the payload");
            }
            _ => {
                let buffer = self.current_page.mem.buffer();
                let page_header = BtreePageHeader::from_page(&self.current_page.mem, &buffer);

                // TODO: Support freeblock.
                assert_eq!(page_header.first_freeblock_offset(), 0);
                assert_eq!(page_header.fragmented_free_bytes(), 0);
                let header_size = page_header.header_size();
                let unallocated_space_offset = cell_pointer_offset(
                    &self.current_page.mem,
                    self.current_page.n_cells,
                    header_size,
                );
                assert!(unallocated_space_offset > 0);
                let cell_content_area_offset =
                    page_header.cell_content_area_offset().get() as usize;
                if cell_content_area_offset < unallocated_space_offset {
                    bail!("invalid cell content area offset");
                }

                let free_size = cell_content_area_offset - unallocated_space_offset;
                if free_size < cell_size + 2 {
                    // TODO: balance the btree.
                    todo!("balance the btree");
                }

                // Upgrade the buffer to writable.
                drop(buffer);
                // Upgrading should be success because there must be no buffer reference of the
                // page. We can guarantee it because:
                //
                // * This cursor is the only cursor handling the btree containing the page and
                // * Only the possible reference is the returned payload from
                //   get_table_payload(). However the payload is dropped before calling insert()
                //   which is mutable method.
                let mut buffer = self.pager.make_page_mut(&self.current_page.mem)?;

                // TODO: allocateSpace().
                // 1. Search freeblock first.
                // 2. Defragmentation if needed
                // 3. Allocate space from unallocated space.

                let offset = cell_content_area_offset - cell_size;
                // cell_content_area_offset is less than or equal to 65536. data is not empty.
                // The offset must be less than 65536 and safe to cast into u16.
                assert!(offset <= u16::MAX as usize);

                // Update the page header.
                let mut page_header =
                    BtreePageHeaderMut::from_page(&self.current_page.mem, &mut buffer);
                // New cell content area offset must not be less than the tail of cell pointers.
                assert!(offset >= unallocated_space_offset + 2);
                // offset <= u16::MAX is asserted above.
                page_header.set_cell_content_area_offset(offset as u16);
                self.current_page.n_cells += 1;
                page_header.set_n_cells(self.current_page.n_cells);

                // Update cell pointer.
                let cell_pointer_offset = if current_cell_key.is_some() {
                    // Insert the new cell between cells.
                    let cell_pointer_offset = cell_pointer_offset(
                        &self.current_page.mem,
                        self.current_page.idx_cell,
                        header_size,
                    );
                    buffer.copy_within(
                        cell_pointer_offset..unallocated_space_offset,
                        cell_pointer_offset + 2,
                    );
                    cell_pointer_offset
                } else {
                    // Append the new cell to the tail.
                    unallocated_space_offset
                };
                buffer[cell_pointer_offset..cell_pointer_offset + 2]
                    .copy_from_slice(&(offset as u16).to_be_bytes());

                // Copy payload to the btree page.
                let payload_offset = offset + cell_header_size;
                buffer[offset..payload_offset].copy_from_slice(&cell_header[..cell_header_size]);
                let payload_tail_offset = payload_offset + n_local;
                buffer[payload_offset..payload_tail_offset].copy_from_slice(&payload[..n_local]);
                if let Some(overflow_page_id) = overflow_page_id {
                    assert_eq!(overflow_page_id.len(), 4);
                    buffer[payload_tail_offset..payload_tail_offset + overflow_page_id.len()]
                        .copy_from_slice(&overflow_page_id);
                }
            }
        }
        Ok(())
    }

    pub fn get_table_key(&self) -> anyhow::Result<Option<i64>> {
        if !self.initialized {
            bail!("cursor is not initialized");
        }
        if !self.current_page.page_type.is_table() {
            bail!("not a table page");
        }
        if self.current_page.idx_cell >= self.current_page.n_cells {
            return Ok(None);
        }
        assert!(self.current_page.is_leaf);
        let buffer = self.current_page.mem.buffer();
        let cell_key_parser = TableCellKeyParser::new(&self.current_page.mem, &buffer);
        let key = cell_key_parser
            .get_cell_key(self.current_page.idx_cell)
            .map_err(|e| anyhow::anyhow!("parse table cell key: {:?}", e))?;
        Ok(Some(key))
    }

    pub fn get_table_payload(&self) -> anyhow::Result<Option<(i64, BtreePayload)>> {
        if !self.initialized {
            bail!("cursor is not initialized");
        }
        if !self.current_page.page_type.is_table() {
            bail!("not a table page");
        }
        if self.current_page.idx_cell >= self.current_page.n_cells {
            return Ok(None);
        }
        assert!(self.current_page.is_leaf);
        let buffer = self.current_page.mem.buffer();
        let (key, payload_info) = parse_btree_leaf_table_cell(
            self.btree_ctx,
            &self.current_page.mem,
            &buffer,
            self.current_page.idx_cell,
        )
        .map_err(|e| anyhow::anyhow!("parse btree leaf table cell: {:?}", e))?;
        Ok(Some((
            key,
            BtreePayload {
                pager: self.pager,
                bctx: self.btree_ctx,
                local_payload_buffer: buffer,
                payload_info,
            },
        )))
    }

    pub fn get_index_payload(&self) -> anyhow::Result<Option<BtreePayload>> {
        if !self.initialized {
            bail!("cursor is not initialized");
        }
        if !self.current_page.page_type.is_index() {
            bail!("not a index page");
        }
        if self.current_page.idx_cell >= self.current_page.n_cells {
            return Ok(None);
        }
        let buffer = self.current_page.mem.buffer();
        let cell_key_parser =
            IndexCellKeyParser::new(self.btree_ctx, &self.current_page.mem, &buffer);
        let payload_info = cell_key_parser
            .get_cell_key(self.current_page.idx_cell)
            .map_err(|e| anyhow::anyhow!("parse btree leaf index cell: {:?}", e))?;
        Ok(Some(BtreePayload {
            pager: self.pager,
            bctx: self.btree_ctx,
            local_payload_buffer: buffer,
            payload_info,
        }))
    }

    /// Move to the left most cell in its child and grand child page.
    ///
    /// The cursor must points to a interior page.
    /// If cursor is completed, return `Ok(false)`.
    fn move_to_left_most(&mut self) -> anyhow::Result<bool> {
        assert!(!self.current_page.is_leaf);
        let buffer = self.current_page.mem.buffer();
        let page_id = match self.current_page.idx_cell.cmp(&self.current_page.n_cells) {
            Ordering::Less => parse_btree_interior_cell_page_id(
                &self.current_page.mem,
                &buffer,
                self.current_page.idx_cell,
            )
            .map_err(|e| anyhow::anyhow!("get btree interior cell page id: {:?}", e))?,
            Ordering::Equal => {
                let page_header = BtreePageHeader::from_page(&self.current_page.mem, &buffer);
                page_header.right_page_id()
            }
            Ordering::Greater => {
                // The cursor traversed all cells in the interior page.
                return Ok(false);
            }
        };
        drop(buffer);
        self.move_to_child(page_id)?;
        self.current_page.idx_cell = 0;
        loop {
            if self.current_page.is_leaf {
                break;
            }
            let buffer = self.current_page.mem.buffer();
            let page_id = parse_btree_interior_cell_page_id(&self.current_page.mem, &buffer, 0)
                .map_err(|e| anyhow::anyhow!("get btree interior cell page id: {:?}", e))?;
            drop(buffer);
            self.move_to_child(page_id)?;
        }
        Ok(true)
    }

    fn move_to_root(&mut self) -> anyhow::Result<()> {
        if !self.parent_pages.is_empty() {
            self.parent_pages.truncate(1);
            self.current_page = self.parent_pages.pop().unwrap();
        }
        Ok(())
    }

    fn move_to_child(&mut self, page_id: PageId) -> anyhow::Result<()> {
        let mem = self.pager.get_page(page_id)?;
        let mut page = CursorPage::new(mem);
        std::mem::swap(&mut self.current_page, &mut page);
        self.parent_pages.push(page);
        Ok(())
    }

    fn back_to_parent(&mut self) -> anyhow::Result<bool> {
        let Some(page) = self.parent_pages.pop() else {
            return Ok(false);
        };
        self.current_page = page;
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pager::MAX_PAGE_SIZE;
    use crate::record::parse_record;
    use crate::test_utils::*;
    use crate::value::Collation;
    use crate::value::Value;

    #[test]
    fn test_btree_cursor_single_table_page() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "INSERT INTO example(col) VALUES (0);",
            "INSERT INTO example(col) VALUES (1);",
            "INSERT INTO example(col) VALUES (2);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();

        cursor.move_to_first().unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_some());
        let (key, payload) = payload.unwrap();
        assert_eq!(key, 1);
        assert_eq!(payload.buf(), &[2, 8]);
        assert_eq!(payload.size(), payload.buf().len() as i32);
        assert!(cursor.get_index_payload().is_err());
        drop(payload);
        assert_eq!(cursor.get_table_key().unwrap().unwrap(), 1);

        cursor.move_next().unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_some());
        let (key, payload) = payload.unwrap();
        assert_eq!(key, 2);
        assert_eq!(payload.buf(), &[2, 9]);
        assert_eq!(payload.size(), payload.buf().len() as i32);
        assert!(cursor.get_index_payload().is_err());
        drop(payload);
        assert_eq!(cursor.get_table_key().unwrap().unwrap(), 2);

        cursor.move_next().unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_some());
        let (key, payload) = payload.unwrap();
        assert_eq!(key, 3);
        assert_eq!(payload.buf(), &[2, 1, 2]);
        assert_eq!(payload.size(), payload.buf().len() as i32);
        assert!(cursor.get_index_payload().is_err());
        drop(payload);
        assert_eq!(cursor.get_table_key().unwrap().unwrap(), 3);

        cursor.move_next().unwrap();
        assert!(cursor.get_table_payload().unwrap().is_none());
        assert!(cursor.get_index_payload().is_err());
        assert!(cursor.get_table_key().unwrap().is_none());

        cursor.move_to_last().unwrap();
        assert_eq!(cursor.get_table_key().unwrap().unwrap(), 3);

        cursor.move_to_first().unwrap();
        cursor.move_to_last().unwrap();
        assert_eq!(cursor.get_table_key().unwrap().unwrap(), 3);
    }

    #[test]
    fn test_btree_cursor_single_index_page() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE INDEX index1 ON example(col);",
            "INSERT INTO example(col) VALUES (1);",
            "INSERT INTO example(col) VALUES (0);",
            "INSERT INTO example(col) VALUES (2);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_index_page_id("index1", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();

        cursor.move_to_first().unwrap();
        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_some());
        let payload = payload.unwrap();
        assert_eq!(payload.buf(), &[3, 8, 1, 2]);
        assert_eq!(payload.size(), payload.buf().len() as i32);
        assert!(cursor.get_table_payload().is_err());
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_some());
        let payload = payload.unwrap();
        assert_eq!(payload.buf(), &[3, 9, 9]);
        assert_eq!(payload.size(), payload.buf().len() as i32);
        assert!(cursor.get_table_payload().is_err());
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_some());
        let payload = payload.unwrap();
        assert_eq!(payload.buf(), &[3, 1, 1, 2, 3]);
        assert_eq!(payload.size(), payload.buf().len() as i32);
        assert!(cursor.get_table_payload().is_err());
        drop(payload);

        cursor.move_next().unwrap();
        assert!(cursor.get_index_payload().unwrap().is_none());
        assert!(cursor.get_table_payload().is_err());

        cursor.move_to_last().unwrap();
        assert_eq!(
            cursor.get_index_payload().unwrap().unwrap().buf(),
            &[3, 1, 1, 2, 3]
        );

        cursor.move_to_first().unwrap();
        cursor.move_to_last().unwrap();
        assert_eq!(
            cursor.get_index_payload().unwrap().unwrap().buf(),
            &[3, 1, 1, 2, 3]
        );
    }

    #[test]
    fn test_cursor_uninitialized() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE INDEX index1 ON example(col);",
            "INSERT INTO example(col) VALUES (0);",
            "INSERT INTO example(col) VALUES (1);",
            "INSERT INTO example(col) VALUES (2);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());
        let index_page_id = find_index_page_id("index1", file.path());

        let mut table_cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();
        let mut index_cursor = BtreeCursor::new(index_page_id, &pager, &bctx).unwrap();

        assert!(table_cursor.move_next().is_err());
        assert!(table_cursor.get_table_payload().is_err());
        assert!(index_cursor.move_next().is_err());
        assert!(index_cursor.get_index_payload().is_err());
    }

    #[test]
    fn test_btree_cursor_empty_table() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();
        cursor.move_to_first().unwrap();
        assert!(cursor.get_table_payload().unwrap().is_none());
        cursor.move_next().unwrap();
        assert!(cursor.get_table_payload().unwrap().is_none());
        assert!(cursor.table_move_to(0).unwrap().is_none());
        assert!(cursor.get_table_payload().unwrap().is_none());
        cursor.move_to_last().unwrap();
        assert!(cursor.get_table_payload().unwrap().is_none());
    }

    #[test]
    fn test_btree_cursor_empty_index() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE INDEX index1 ON example(col);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_index_page_id("index1", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();
        cursor.move_to_first().unwrap();
        assert!(cursor.get_index_payload().unwrap().is_none());
        cursor.move_next().unwrap();
        assert!(cursor.get_index_payload().unwrap().is_none());
        cursor
            .index_move_to(&[ValueCmp::new(&Value::Integer(0), &Collation::Binary)])
            .unwrap();
        assert!(cursor.get_index_payload().unwrap().is_none());
        cursor.move_to_last().unwrap();
        assert!(cursor.get_index_payload().unwrap().is_none());
    }

    #[test]
    fn test_btree_cursor_multiple_level_pages() {
        // index record has 1 (header length) + 2 (bytes) + 1 (integer) bytes header +
        // at most 2 (integer) rowid.
        const BUFFER_SIZE: usize = 994;
        let buf = vec![0; BUFFER_SIZE];
        let hex = buffer_to_hex(&buf);
        let mut inserts = Vec::new();
        // 4 entries with 1000 byte blob occupies 1 page. These 4000 entries introduce 2
        // level interior pages and 1 leaf page level.
        for i in 0..4000 {
            inserts.push(format!(
                "INSERT INTO example(col,buf) VALUES ({},X'{}');",
                i,
                hex.as_str()
            ));
        }
        for i in 4000..5000 {
            inserts.push(format!(
                "INSERT INTO example(col,buf) VALUES ({},X'FF');",
                i
            ));
        }
        let mut queries = vec![
            "CREATE TABLE example(col,buf);",
            "CREATE INDEX index1 ON example(buf);",
            "CREATE INDEX index2 ON example(col);",
        ];
        queries.extend(inserts.iter().map(|s| s.as_str()));
        let file = create_sqlite_database(&queries);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());
        let index1_page_id = find_index_page_id("index1", file.path());
        let index2_page_id = find_index_page_id("index2", file.path());

        let mut table_cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();
        table_cursor.move_to_first().unwrap();
        let mut index1_cursor = BtreeCursor::new(index1_page_id, &pager, &bctx).unwrap();
        index1_cursor.move_to_first().unwrap();
        let mut index2_cursor = BtreeCursor::new(index2_page_id, &pager, &bctx).unwrap();
        index2_cursor.move_to_first().unwrap();

        for i in 0..4000 {
            let payload = table_cursor.get_table_payload().unwrap();
            assert!(payload.is_some());
            let (rowid, payload) = payload.unwrap();
            assert_eq!(rowid, i + 1);
            assert!(payload.size() > BUFFER_SIZE as i32);
            assert_eq!(payload.size(), payload.buf().len() as i32);
            let mut table_record = parse_record(&payload).unwrap();
            assert_eq!(table_record.get(0).unwrap(), Value::Integer(i));
            drop(payload);
            assert_eq!(table_cursor.get_table_key().unwrap().unwrap(), i + 1);
            table_cursor.move_next().unwrap();

            let payload = index1_cursor.get_index_payload().unwrap();
            let payload = payload.unwrap();
            let mut index_record = parse_record(&payload).unwrap();
            assert_eq!(index_record.get(1).unwrap(), Value::Integer(i + 1));
            assert!(payload.size() > BUFFER_SIZE as i32, "{}", i);
            assert_eq!(payload.size(), payload.buf().len() as i32);
            drop(payload);
            index1_cursor.move_next().unwrap();

            let payload = index2_cursor.get_index_payload().unwrap();
            let payload = payload.unwrap();
            let mut index_record = parse_record(&payload).unwrap();
            assert_eq!(index_record.get(0).unwrap(), Value::Integer(i));
            assert_eq!(index_record.get(1).unwrap(), Value::Integer(i + 1));
            assert_eq!(payload.size(), payload.buf().len() as i32);
            drop(payload);
            index2_cursor.move_next().unwrap();
        }
        for i in 4000..5000 {
            let payload = table_cursor.get_table_payload().unwrap();
            assert!(payload.is_some());
            let (rowid, payload) = payload.unwrap();
            assert_eq!(rowid, i + 1);
            let col_buf = (i as u16).to_be_bytes();
            assert_eq!(payload.buf(), &[3, 2, 14, col_buf[0], col_buf[1], 0xff]);
            assert_eq!(payload.size(), payload.buf().len() as i32);
            drop(payload);
            assert_eq!(table_cursor.get_table_key().unwrap().unwrap(), i + 1);
            table_cursor.move_next().unwrap();

            let payload = index1_cursor.get_index_payload().unwrap();
            let payload = payload.unwrap();
            let mut index_record = parse_record(&payload).unwrap();
            assert_eq!(index_record.get(1).unwrap(), Value::Integer(i + 1));
            let rowid_buf = (i as u16 + 1).to_be_bytes();
            assert_eq!(payload.buf(), &[3, 14, 2, 0xff, rowid_buf[0], rowid_buf[1]]);
            assert_eq!(payload.size(), payload.buf().len() as i32);
            drop(payload);
            index1_cursor.move_next().unwrap();

            let payload = index2_cursor.get_index_payload().unwrap();
            let payload = payload.unwrap();
            let mut index_record = parse_record(&payload).unwrap();
            assert_eq!(index_record.get(0).unwrap(), Value::Integer(i));
            assert_eq!(index_record.get(1).unwrap(), Value::Integer(i + 1));
            assert_eq!(payload.size(), payload.buf().len() as i32);
            drop(payload);
            index2_cursor.move_next().unwrap();
        }

        assert!(table_cursor.get_table_payload().unwrap().is_none());
        assert!(index1_cursor.get_index_payload().unwrap().is_none());

        // move_to_last() for table
        table_cursor.move_to_last().unwrap();
        assert_eq!(table_cursor.get_table_key().unwrap().unwrap(), 5000);
        table_cursor.table_move_to(1000).unwrap();
        table_cursor.move_to_last().unwrap();
        assert_eq!(table_cursor.get_table_key().unwrap().unwrap(), 5000);

        // move_to_last() for index
        index1_cursor.move_to_last().unwrap();
        assert_eq!(
            parse_record(&index1_cursor.get_index_payload().unwrap().unwrap())
                .unwrap()
                .get(1)
                .unwrap(),
            Value::Integer(5000)
        );
        index1_cursor
            .index_move_to(&[ValueCmp::new(&Value::Integer(1000), &Collation::Binary)])
            .unwrap();
        index1_cursor.move_to_last().unwrap();
        assert_eq!(
            parse_record(&index1_cursor.get_index_payload().unwrap().unwrap())
                .unwrap()
                .get(1)
                .unwrap(),
            Value::Integer(5000)
        );

        table_cursor.table_move_to(2000).unwrap();
        let payload = table_cursor.get_table_payload().unwrap();
        assert!(payload.is_some());
        let (rowid, _) = payload.unwrap();
        assert_eq!(rowid, 2000);

        index2_cursor
            .index_move_to(&[ValueCmp::new(&Value::Integer(2000), &Collation::Binary)])
            .unwrap();
        let payload = index2_cursor.get_index_payload().unwrap();
        let payload = payload.unwrap();
        let mut index_record = parse_record(&payload).unwrap();
        assert_eq!(index_record.get(0).unwrap(), Value::Integer(2000));
        assert_eq!(index_record.get(1).unwrap(), Value::Integer(2001));
        assert_eq!(payload.size(), payload.buf().len() as i32);
        drop(payload);

        index2_cursor
            .index_move_to(&[
                ValueCmp::new(&Value::Integer(3000), &Collation::Binary),
                ValueCmp::new(&Value::Integer(3001), &Collation::Binary),
            ])
            .unwrap();
        let payload = index2_cursor.get_index_payload().unwrap();
        let payload = payload.unwrap();
        let mut index_record = parse_record(&payload).unwrap();
        assert_eq!(index_record.get(0).unwrap(), Value::Integer(3000));
        assert_eq!(index_record.get(1).unwrap(), Value::Integer(3001));
        assert_eq!(payload.size(), payload.buf().len() as i32);
        drop(payload);

        index2_cursor
            .index_move_to(&[
                ValueCmp::new(&Value::Integer(3000), &Collation::Binary),
                ValueCmp::new(&Value::Integer(3003), &Collation::Binary),
            ])
            .unwrap();
        let payload = index2_cursor.get_index_payload().unwrap();
        let payload = payload.unwrap();
        let mut index_record = parse_record(&payload).unwrap();
        assert_eq!(index_record.get(0).unwrap(), Value::Integer(3001));
        assert_eq!(index_record.get(1).unwrap(), Value::Integer(3002));
        assert_eq!(payload.size(), payload.buf().len() as i32);
        drop(payload);
    }

    #[test]
    fn test_overflow_payload() {
        let mut queries = vec![
            "CREATE TABLE example(col);",
            "CREATE INDEX index1 ON example(col);",
        ];
        let mut buf = Vec::with_capacity(10000);
        for _ in 0..10000 {
            buf.push(rand::random::<u8>());
        }
        let query = format!(
            "INSERT INTO example(col) VALUES (X'{}');",
            buffer_to_hex(&buf)
        );
        queries.push(&query);
        let file = create_sqlite_database(&queries);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();
        cursor.move_to_first().unwrap();

        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_some());
        let (_, payload) = payload.unwrap();

        assert_eq!(payload.buf().len(), 1820);
        assert_eq!(payload.size(), 10004);

        let mut payload_buf = vec![0; 10010];
        let n = payload.load(0, &mut payload_buf).unwrap();
        assert_eq!(n, 10004);
        assert_eq!(payload_buf[0..4], [0x04, 0x81, 0x9c, 0x2c]);
        assert_eq!(&payload_buf[..payload.buf().len()], payload.buf());
        assert_eq!(payload_buf[4..10004], buf);

        let n = payload.load(3000, &mut payload_buf).unwrap();
        assert_eq!(n, 7004);
        assert_eq!(payload_buf[..7004], buf[2996..]);

        let n = payload.load(104, &mut payload_buf[..100]).unwrap();
        assert_eq!(n, 100);
        assert_eq!(payload_buf[..100], buf[100..200]);

        let n = payload.load(3000, &mut payload_buf[..100]).unwrap();
        assert_eq!(n, 100);
        assert_eq!(payload_buf[..100], buf[2996..3096]);

        let result = payload.load(10004, &mut payload_buf);
        assert!(result.is_err());

        let index_page_id = find_index_page_id("index1", file.path());

        let mut cursor = BtreeCursor::new(index_page_id, &pager, &bctx).unwrap();
        cursor.move_to_first().unwrap();

        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_some());
        let payload = payload.unwrap();

        assert_eq!(payload.buf().len(), 489);
        assert_eq!(payload.size(), 10004 + 1);

        let mut payload_buf = vec![0; 10010];
        let n = payload.load(0, &mut payload_buf).unwrap();
        assert_eq!(n, 10004 + 1);
        assert_eq!(payload_buf[0..5], [0x05, 0x81, 0x9c, 0x2c, 0x09]);
        assert_eq!(&payload_buf[..payload.buf().len()], payload.buf());
        assert_eq!(payload_buf[5..10005], buf);

        let n = payload.load(3001, &mut payload_buf).unwrap();
        assert_eq!(n, 7004);
        assert_eq!(payload_buf[..7004], buf[2996..]);

        let n = payload.load(105, &mut payload_buf[..100]).unwrap();
        assert_eq!(n, 100);
        assert_eq!(payload_buf[..100], buf[100..200]);

        let n = payload.load(3001, &mut payload_buf[..100]).unwrap();
        assert_eq!(n, 100);
        assert_eq!(payload_buf[..100], buf[2996..3096]);

        let result = payload.load(10005, &mut payload_buf);
        assert!(result.is_err());
    }

    #[test]
    fn test_table_move_to_in_single_page() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "INSERT INTO example(rowid) VALUES (1);",
            "INSERT INTO example(rowid) VALUES (3);",
            "INSERT INTO example(rowid) VALUES (5);",
            "INSERT INTO example(rowid) VALUES (7);",
            "INSERT INTO example(rowid) VALUES (9);",
            "INSERT INTO example(rowid) VALUES (11);",
            "INSERT INTO example(rowid) VALUES (13);",
            "INSERT INTO example(rowid) VALUES (15);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();

        for i in 0..8 {
            let cell_key = cursor.table_move_to(2 * i).unwrap();
            assert!(cell_key.is_some());
            assert_eq!(cell_key.unwrap(), 2 * i + 1);
            let payload = cursor.get_table_payload().unwrap();
            assert!(payload.is_some());
            let (key, _) = payload.unwrap();
            assert_eq!(key, 2 * i + 1);

            let cell_key = cursor.table_move_to(2 * i + 1).unwrap();
            assert!(cell_key.is_some());
            assert_eq!(cell_key.unwrap(), 2 * i + 1);
            let payload = cursor.get_table_payload().unwrap();
            assert!(payload.is_some());
            let (key, _) = payload.unwrap();
            assert_eq!(key, 2 * i + 1);
        }

        let cell_key = cursor.table_move_to(16).unwrap();
        assert!(cell_key.is_none());
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_none());
    }

    #[test]
    fn test_table_move_to_empty_rows() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();

        for i in 0..3 {
            let cell_key = cursor.table_move_to(i).unwrap();
            assert!(cell_key.is_none());
            let payload = cursor.get_table_payload().unwrap();
            assert!(payload.is_none());
        }
    }

    #[test]
    fn test_table_move_to_multiple_page() {
        let buf = vec![0; 4000];
        let hex = buffer_to_hex(&buf);
        let mut inserts = Vec::new();
        // 1000 byte blob entry occupies 1 page. These 2000 entries introduce
        // 2 level interior pages and 1 leaf page level.
        for i in 0..1000 {
            inserts.push(format!(
                "INSERT INTO example(rowid, col) VALUES ({},X'{}');",
                2 * i + 1,
                hex.as_str()
            ));
        }
        for i in 1000..2000 {
            inserts.push(format!(
                "INSERT INTO example(rowid) VALUES ({});",
                2 * i + 1
            ));
        }
        let mut queries = vec!["CREATE TABLE example(col);"];
        queries.extend(inserts.iter().map(|s| s.as_str()));
        let file = create_sqlite_database(&queries);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();

        for i in 0..2000 {
            let cell_key = cursor.table_move_to(2 * i).unwrap();
            assert!(cell_key.is_some());
            assert_eq!(cell_key.unwrap(), 2 * i + 1);
            let payload = cursor.get_table_payload().unwrap();
            assert!(payload.is_some());
            let (key, _) = payload.unwrap();
            assert_eq!(key, 2 * i + 1);

            let cell_key = cursor.table_move_to(2 * i + 1).unwrap();
            assert!(cell_key.is_some());
            assert_eq!(cell_key.unwrap(), 2 * i + 1);
            let payload = cursor.get_table_payload().unwrap();
            assert!(payload.is_some());
            let (key, _) = payload.unwrap();
            assert_eq!(key, 2 * i + 1);
        }

        let cell_key = cursor.table_move_to(40002).unwrap();
        assert!(cell_key.is_none());
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_none());
    }

    #[test]
    fn test_index_move_to_in_single_page() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE INDEX index1 ON example(col);",
            "INSERT INTO example(rowid, col) VALUES (1, 1);",
            "INSERT INTO example(rowid, col) VALUES (3, 3);",
            "INSERT INTO example(rowid, col) VALUES (5, 5);",
            "INSERT INTO example(rowid, col) VALUES (10, 10);",
            "INSERT INTO example(rowid, col) VALUES (11, 10);",
            "INSERT INTO example(rowid, col) VALUES (12, 10);",
            "INSERT INTO example(rowid, col) VALUES (15, 11);",
            "INSERT INTO example(rowid, col) VALUES (14, 11);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_index_page_id("index1", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();

        for i in 0..3 {
            cursor
                .index_move_to(&[ValueCmp::new(&Value::Integer(2 * i), &Collation::Binary)])
                .unwrap();
            let payload = cursor.get_index_payload().unwrap();
            assert!(payload.is_some());
            let mut record = parse_record(payload.as_ref().unwrap()).unwrap();
            assert_eq!(record.get(0).unwrap(), Value::Integer(2 * i + 1));
            assert_eq!(record.get(1).unwrap(), Value::Integer(2 * i + 1));
            drop(payload);

            cursor
                .index_move_to(&[ValueCmp::new(
                    &Value::Integer(2 * i + 1),
                    &Collation::Binary,
                )])
                .unwrap();
            let payload = cursor.get_index_payload().unwrap();
            assert!(payload.is_some());
            let mut record = parse_record(payload.as_ref().unwrap()).unwrap();
            assert_eq!(record.get(0).unwrap(), Value::Integer(2 * i + 1));
            assert_eq!(record.get(1).unwrap(), Value::Integer(2 * i + 1));
        }

        cursor
            .index_move_to(&[ValueCmp::new(&Value::Integer(10), &Collation::Binary)])
            .unwrap();
        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_some());
        let mut record = parse_record(payload.as_ref().unwrap()).unwrap();
        assert_eq!(record.get(0).unwrap(), Value::Integer(10));
        // If there are multiple entries with the same key, one of the entries is
        // returned (not necessarily the first or last one).
        assert_eq!(record.get(1).unwrap(), Value::Integer(11));
        drop(payload);

        for i in 10..13 {
            cursor
                .index_move_to(&[
                    ValueCmp::new(&Value::Integer(10), &Collation::Binary),
                    ValueCmp::new(&Value::Integer(i), &Collation::Binary),
                ])
                .unwrap();
            let payload = cursor.get_index_payload().unwrap();
            assert!(payload.is_some());
            let mut record = parse_record(payload.as_ref().unwrap()).unwrap();
            assert_eq!(record.get(0).unwrap(), Value::Integer(10));
            assert_eq!(record.get(1).unwrap(), Value::Integer(i));
        }

        cursor
            .index_move_to(&[
                ValueCmp::new(&Value::Integer(10), &Collation::Binary),
                ValueCmp::new(&Value::Integer(13), &Collation::Binary),
            ])
            .unwrap();
        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_some());
        let mut record = parse_record(payload.as_ref().unwrap()).unwrap();
        assert_eq!(record.get(0).unwrap(), Value::Integer(11));
        assert_eq!(record.get(1).unwrap(), Value::Integer(14));
        drop(payload);

        cursor
            .index_move_to(&[
                ValueCmp::new(&Value::Integer(11), &Collation::Binary),
                ValueCmp::new(&Value::Integer(16), &Collation::Binary),
            ])
            .unwrap();
        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_none());
    }

    #[test]
    fn test_index_move_to_multi_column() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col1, col2);",
            "CREATE INDEX index1 ON example(col1, col2);",
            "INSERT INTO example(col1, col2) VALUES (1, NULL);",
            "INSERT INTO example(col1, col2) VALUES (1, NULL);",
            "INSERT INTO example(col1, col2) VALUES (1, -10);",
            "INSERT INTO example(col1, col2) VALUES (1, 2);",
            "INSERT INTO example(col1, col2) VALUES (1, 5.1);",
            "INSERT INTO example(col1, col2) VALUES (1, 100);",
            "INSERT INTO example(col1, col2) VALUES (1, '');",
            "INSERT INTO example(col1, col2) VALUES (1, '0123');",
            "INSERT INTO example(col1, col2) VALUES (1, '0123');",
            "INSERT INTO example(col1, col2) VALUES (1, '0124');",
            "INSERT INTO example(col1, col2) VALUES (1, '0125');",
            "INSERT INTO example(col1, col2) VALUES (1, x'0123');",
            "INSERT INTO example(col1, col2) VALUES (1, x'0124');",
            "INSERT INTO example(col1, col2) VALUES (1, x'0125');",
            "INSERT INTO example(col1) VALUES (NULL);",
            "INSERT INTO example(col1) VALUES (-10);",
            "INSERT INTO example(col1) VALUES (2);",
            "INSERT INTO example(col1) VALUES (5.1);",
            "INSERT INTO example(col1) VALUES (100);",
            "INSERT INTO example(col1) VALUES ('');",
            "INSERT INTO example(col1) VALUES ('0123');",
            "INSERT INTO example(col1) VALUES ('0123');",
            "INSERT INTO example(col1) VALUES ('0123');",
            "INSERT INTO example(col1) VALUES ('0124');",
            "INSERT INTO example(col1) VALUES ('0125');",
            "INSERT INTO example(col1) VALUES (x'0123');",
            "INSERT INTO example(col1) VALUES (x'0124');",
            "INSERT INTO example(col1) VALUES (x'0125');",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_index_page_id("index1", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();

        for (expected, keys) in [
            (
                15,
                vec![
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
            (
                1,
                vec![
                    ValueCmp::new(&Value::Integer(1), &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
            (
                2,
                vec![
                    ValueCmp::new(&Value::Integer(1), &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                    ValueCmp::new(&Value::Integer(2), &Collation::Binary),
                ],
            ),
            (
                4,
                vec![
                    ValueCmp::new(&Value::Integer(1), &Collation::Binary),
                    ValueCmp::new(&Value::Integer(0), &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
            (
                3,
                vec![
                    ValueCmp::new(&Value::Integer(1), &Collation::Binary),
                    ValueCmp::new(&Value::Real(-10.1), &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
            (
                5,
                vec![
                    ValueCmp::new(&Value::Integer(1), &Collation::Binary),
                    ValueCmp::new(&Value::Integer(5), &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
            (
                7,
                vec![
                    ValueCmp::new(&Value::Integer(1), &Collation::Binary),
                    ValueCmp::new(&Value::Integer(101), &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
            (
                7,
                vec![
                    ValueCmp::new(&Value::Integer(1), &Collation::Binary),
                    ValueCmp::new(&Value::Text(b"".as_slice().into()), &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
            (
                8,
                vec![
                    ValueCmp::new(&Value::Integer(1), &Collation::Binary),
                    ValueCmp::new(&Value::Text(b"\0".as_slice().into()), &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
            (
                10,
                vec![
                    ValueCmp::new(&Value::Integer(1), &Collation::Binary),
                    ValueCmp::new(&Value::Text(b"01234".as_slice().into()), &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
            (
                10,
                vec![
                    ValueCmp::new(&Value::Integer(1), &Collation::Binary),
                    ValueCmp::new(&Value::Text(b"0124".as_slice().into()), &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
            (
                13,
                vec![
                    ValueCmp::new(&Value::Integer(1), &Collation::Binary),
                    ValueCmp::new(
                        &Value::Blob([0x01, 0x24].as_slice().into()),
                        &Collation::Binary,
                    ),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
            (
                17,
                vec![
                    ValueCmp::new(&Value::Integer(1), &Collation::Binary),
                    ValueCmp::new(
                        &Value::Blob([0x01, 0x26].as_slice().into()),
                        &Collation::Binary,
                    ),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
            (
                17,
                vec![
                    ValueCmp::new(&Value::Integer(2), &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
            (
                18,
                vec![
                    ValueCmp::new(&Value::Integer(3), &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
            (
                21,
                vec![
                    ValueCmp::new(&Value::Text(b"0123".as_slice().into()), &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
            (
                22,
                vec![
                    ValueCmp::new(&Value::Text(b"0123".as_slice().into()), &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                    ValueCmp::new(&Value::Integer(22), &Collation::Binary),
                ],
            ),
            (
                24,
                vec![
                    ValueCmp::new(&Value::Text(b"0123".as_slice().into()), &Collation::Binary),
                    ValueCmp::new(&Value::Integer(1), &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
            (
                27,
                vec![
                    ValueCmp::new(
                        &Value::Blob([0x01, 0x24].as_slice().into()),
                        &Collation::Binary,
                    ),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                    ValueCmp::new(&Value::Null, &Collation::Binary),
                ],
            ),
        ] {
            cursor.index_move_to(&keys).unwrap();
            let payload = cursor.get_index_payload().unwrap();
            assert!(payload.is_some());
            let payload = payload.unwrap();
            let mut record = parse_record(&payload).unwrap();
            if let Value::Integer(rowid) = record.get(record.len() - 1).unwrap() {
                assert_eq!(rowid, expected, "{:?}", keys);
            } else {
                panic!("unexpected payload: {:?}", keys);
            }
        }
    }

    #[test]
    fn test_index_move_to_collate_sequence() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col1 COLLATE BINARY, col2 COLLATE NOCASE, col3 COLLATE RTRIM);",
            "CREATE INDEX index1 ON example(col1);",
            "CREATE INDEX index2 ON example(col2);",
            "CREATE INDEX index3 ON example(col3);",
            "INSERT INTO example(col1, col2, col3) VALUES ('abcde1', 'abcde1', 'abcde1');",
            "INSERT INTO example(col1, col2, col3) VALUES ('abcde2', 'abcde2', 'abcde2');",
            "INSERT INTO example(col1, col2, col3) VALUES ('abcdef  ', 'abcdef  ', 'abcdef  ');",
            "INSERT INTO example(col1, col2, col3) VALUES ('ABCDEF', 'ABCDEF', 'ABCDEF');",
            "INSERT INTO example(col1, col2, col3) VALUES ('ABCDE', 'ABCDE', 'ABCDE');",
            "INSERT INTO example(col1, col2, col3) VALUES ('ABCDE  ', 'ABCDE  ', 'ABCDE  ');",
            "INSERT INTO example(col1, col2, col3) VALUES ('abcde  ', 'abcde  ', 'abcde  ');",
            "INSERT INTO example(col1, col2, col3) VALUES ('abcde', 'abcde', 'abcde');",
            "INSERT INTO example(col1, col2, col3) VALUES ('abcdef', 'abcdef', 'abcdef');",
            "INSERT INTO example(col1, col2, col3) VALUES ('ABCDEF  ', 'ABCDEF  ', 'ABCDEF  ');",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();

        let mut cursor1 =
            BtreeCursor::new(find_index_page_id("index1", file.path()), &pager, &bctx).unwrap();
        let mut cursor2 =
            BtreeCursor::new(find_index_page_id("index2", file.path()), &pager, &bctx).unwrap();
        let mut cursor3 =
            BtreeCursor::new(find_index_page_id("index3", file.path()), &pager, &bctx).unwrap();

        for (expected, key) in [
            ([8, 5, 7], Value::Text(b"abcde".as_slice().into())),
            ([5, 5, 5], Value::Text(b"ABCDE".as_slice().into())),
            ([7, 6, 7], Value::Text(b"abcde  ".as_slice().into())),
            ([6, 6, 5], Value::Text(b"ABCDE  ".as_slice().into())),
            ([9, 4, 3], Value::Text(b"abcdef".as_slice().into())),
            ([4, 4, 4], Value::Text(b"ABCDEF".as_slice().into())),
            ([10, 3, 4], Value::Text(b"ABCDEF  ".as_slice().into())),
        ] {
            let keys = vec![
                ValueCmp::new(&key, &Collation::Binary),
                ValueCmp::new(&Value::Null, &Collation::Binary),
            ];
            cursor1.index_move_to(&keys).unwrap();
            let payload = cursor1.get_index_payload().unwrap();
            assert!(payload.is_some());
            let payload = payload.unwrap();
            let mut record = parse_record(&payload).unwrap();
            if let Value::Integer(rowid) = record.get(record.len() - 1).unwrap() {
                assert_eq!(rowid, expected[0], "{:?}", keys);
            } else {
                panic!("unexpected payload: {:?}", keys);
            }

            let keys = vec![
                ValueCmp::new(&key, &Collation::NoCase),
                ValueCmp::new(&Value::Null, &Collation::Binary),
            ];
            cursor2.index_move_to(&keys).unwrap();
            let payload = cursor2.get_index_payload().unwrap();
            assert!(payload.is_some());
            let payload = payload.unwrap();
            let mut record = parse_record(&payload).unwrap();
            if let Value::Integer(rowid) = record.get(record.len() - 1).unwrap() {
                assert_eq!(rowid, expected[1], "{:?}", keys);
            } else {
                panic!("unexpected payload: {:?}", keys);
            }

            let keys = vec![
                ValueCmp::new(&key, &Collation::RTrim),
                ValueCmp::new(&Value::Null, &Collation::Binary),
            ];
            cursor3.index_move_to(&keys).unwrap();
            let payload = cursor3.get_index_payload().unwrap();
            assert!(payload.is_some());
            let payload = payload.unwrap();
            let mut record = parse_record(&payload).unwrap();
            if let Value::Integer(rowid) = record.get(record.len() - 1).unwrap() {
                assert_eq!(rowid, expected[2], "{:?}", keys);
            } else {
                panic!("unexpected payload: {:?}", keys);
            }
        }
    }

    #[test]
    fn test_index_move_to_empty_rows() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE INDEX index1 ON example(col);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_index_page_id("index1", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();

        for i in 0..3 {
            cursor
                .index_move_to(&[ValueCmp::new(&Value::Integer(i), &Collation::Binary)])
                .unwrap();
            let payload = cursor.get_index_payload().unwrap();
            assert!(payload.is_none());
        }
    }

    #[test]
    fn test_index_move_to_multiple_page() {
        // index record has 1 (header length) + 2 (bytes) + 1 (integer) bytes header +
        // at most 2 (integer) rowid.
        const BUFFER_SIZE: usize = 994;
        let buf = vec![0; BUFFER_SIZE];
        let hex = buffer_to_hex(&buf);
        let mut inserts = Vec::new();
        // 1000 byte blob entry occupies 1 page. These 2000 entries introduce
        // 2 level interior pages and 1 leaf page level.
        for i in 0..4000 {
            inserts.push(format!(
                "INSERT INTO example(rowid, id, col) VALUES ({},{},X'{}');",
                i,
                2 * i + 1,
                hex.as_str()
            ));
        }
        for i in 4000..5000 {
            inserts.push(format!(
                "INSERT INTO example(rowid,id, col) VALUES ({},{}, X'FFFFFFFF');",
                i,
                2 * i + 1
            ));
        }
        let mut queries = vec![
            "CREATE TABLE example(id, col);",
            "CREATE INDEX index1 ON example(id, col);",
        ];
        queries.extend(inserts.iter().map(|s| s.as_str()));
        let file = create_sqlite_database(&queries);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_index_page_id("index1", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();

        for i in 0..2000 {
            cursor
                .index_move_to(&[ValueCmp::new(&Value::Integer(2 * i), &Collation::Binary)])
                .unwrap();
            let payload = cursor.get_index_payload().unwrap();
            assert!(payload.is_some(), "i = {}", i);
            let mut record = parse_record(payload.as_ref().unwrap()).unwrap();
            assert_eq!(record.get(0).unwrap(), Value::Integer(2 * i + 1));
            assert_eq!(record.get(2).unwrap(), Value::Integer(i));
            drop(payload);

            // Reset the cursor.
            cursor.move_to_first().unwrap();

            cursor
                .index_move_to(&[ValueCmp::new(
                    &Value::Integer(2 * i + 1),
                    &Collation::Binary,
                )])
                .unwrap();
            let payload = cursor.get_index_payload().unwrap();
            assert!(payload.is_some(), "i = {}", i);
            let mut record = parse_record(payload.as_ref().unwrap()).unwrap();
            assert_eq!(record.get(0).unwrap(), Value::Integer(2 * i + 1));
            assert_eq!(record.get(2).unwrap(), Value::Integer(i));
            drop(payload);

            // Reset the cursor.
            cursor.move_to_first().unwrap();
        }

        cursor
            .index_move_to(&[ValueCmp::new(&Value::Integer(10000), &Collation::Binary)])
            .unwrap();
        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_none());
    }

    #[test]
    fn test_insert_empty_table() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();

        cursor.insert(1, &[1]).unwrap();
        cursor.move_to_first().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 1);
        assert_eq!(payload.buf(), &[1]);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_none());
        drop(payload);

        cursor.insert(2, &[2, 3]).unwrap();
        cursor.insert(4, &[4, 5, 6, 7]).unwrap();

        cursor.move_to_first().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 1);
        assert_eq!(payload.buf(), &[1]);
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 2);
        assert_eq!(payload.buf(), &[2, 3]);
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 4);
        assert_eq!(payload.buf(), &[4, 5, 6, 7]);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_none());
        drop(payload);

        cursor.insert(-1, &[255]).unwrap();
        cursor.insert(3, &[]).unwrap();

        cursor.move_to_first().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, -1);
        assert_eq!(payload.buf(), &[255]);
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 1);
        assert_eq!(payload.buf(), &[1]);
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 2);
        assert_eq!(payload.buf(), &[2, 3]);
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 3);
        assert_eq!(payload.buf(), &[]);
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 4);
        assert_eq!(payload.buf(), &[4, 5, 6, 7]);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_none());
        drop(payload);
    }

    #[test]
    fn test_insert_existing_table() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "INSERT INTO example(col) VALUES (1);", // rowid = 1
            "INSERT INTO example(col) VALUES (2);", // rowid = 2
            "INSERT INTO example(rowid, col) VALUES (5, 5);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();

        cursor.insert(6, &[6]).unwrap();
        cursor.insert(-1, &[255]).unwrap();
        cursor.insert(3, &[3]).unwrap();

        cursor.move_to_first().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, -1);
        assert_eq!(payload.buf(), &[255]);
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 1);
        assert_eq!(
            parse_record(&payload).unwrap().get(0).unwrap(),
            Value::Integer(1)
        );
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 2);
        assert_eq!(
            parse_record(&payload).unwrap().get(0).unwrap(),
            Value::Integer(2)
        );
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 3);
        assert_eq!(payload.buf(), &[3]);
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 5);
        assert_eq!(
            parse_record(&payload).unwrap().get(0).unwrap(),
            Value::Integer(5)
        );
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 6);
        assert_eq!(payload.buf(), &[6]);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_none());
        drop(payload);
    }

    #[test]
    fn test_insert_max_page_size() {
        let file =
            create_sqlite_database(&["PRAGMA page_size = 65536;", "CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());

        let page_1 = pager.get_page(1).unwrap();
        assert_eq!(page_1.buffer().len(), MAX_PAGE_SIZE);
        assert_eq!(bctx.usable_size as usize, MAX_PAGE_SIZE);
        drop(page_1);
        let page_2 = pager.get_page(table_page_id).unwrap();
        let buffer = page_2.buffer();
        let header = BtreePageHeader::from_page(&page_2, &buffer);
        assert_eq!(
            header.cell_content_area_offset().get() as usize,
            MAX_PAGE_SIZE
        );
        drop(buffer);
        drop(page_2);

        let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();

        // cell_content_area_offset zero must be translated as 65536 and inserting must
        // succeed.
        cursor.insert(1, &[1]).unwrap();
        cursor.move_to_first().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 1);
        assert_eq!(payload.buf(), &[1]);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_none());
        drop(payload);
    }

    #[test]
    fn test_insert_overflow() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);

        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());
        let max_local = bctx.max_local(true) as usize;
        let usable_size = bctx.usable_size as usize;

        let mut data = Vec::with_capacity(usable_size * 2);
        for _ in 0..usable_size * 2 {
            data.push(rand::random::<u8>());
        }

        // Not overflow
        {
            let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();
            cursor.insert(1, &data[..max_local]).unwrap();
            cursor.table_move_to(1).unwrap();
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, 1);
            assert_eq!(payload.size() as usize, max_local);
            assert_eq!(payload.buf().len(), max_local);
            assert_eq!(payload.buf(), &data[..max_local]);
        }
        pager.abort();

        // Overflows
        let payload_size = max_local + 1;
        {
            let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();
            cursor.insert(2, &data[..payload_size]).unwrap();
            cursor.table_move_to(2).unwrap();
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, 2);
            assert_eq!(payload.size() as usize, payload_size);
            assert!(payload.buf().len() < payload_size);
            let mut buf = vec![0; payload_size + 1];
            let loaded = payload.load(0, &mut buf).unwrap();
            assert_eq!(loaded, payload_size);
            assert_eq!(&buf[..payload_size], &data[..payload_size]);
        }
        pager.abort();

        // Overflows with exact overflow page size
        let mut size_exact_overflow_page_size = -1;
        for i in 1..4096 {
            let p_size = max_local + i;
            let n_local = bctx.n_local(true, p_size as i32) as usize;
            if (p_size - n_local) % (bctx.usable_size as usize - 4) == 0 {
                size_exact_overflow_page_size = p_size as i32;
                break;
            }
        }
        assert!(size_exact_overflow_page_size > 0);
        assert_eq!(size_exact_overflow_page_size, 4581);
        let payload_size = size_exact_overflow_page_size as usize;
        {
            let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();
            cursor.insert(3, &data[..payload_size]).unwrap();
            cursor.table_move_to(3).unwrap();
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, 3);
            assert_eq!(payload.size() as usize, payload_size);
            assert!(payload.buf().len() < payload_size);
            let mut buf = vec![0; payload_size + 1];
            let loaded = payload.load(0, &mut buf).unwrap();
            assert_eq!(loaded, payload_size);
            assert_eq!(&buf[..payload_size], &data[..payload_size]);
        }
        pager.abort();

        // Overflow with multiple overflow pages.
        let payload_size = usable_size * 2;
        {
            let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();
            cursor.insert(4, &data[..payload_size]).unwrap();
            cursor.table_move_to(4).unwrap();
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, 4);
            assert_eq!(payload.size() as usize, payload_size);
            assert!(payload.buf().len() < payload_size);
            let mut buf = vec![0; payload_size + 1];
            let loaded = payload.load(0, &mut buf).unwrap();
            assert_eq!(loaded, payload_size);
            assert_eq!(&buf[..payload_size], &data[..payload_size]);
        }
        pager.abort();
    }
}
