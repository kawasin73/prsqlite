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
use std::fmt::Display;

use crate::btree::allocate_from_freeblocks;
use crate::btree::allocate_from_unallocated_space;
use crate::btree::cell_pointer_offset;
use crate::btree::compute_free_size;
use crate::btree::get_cell_offset;
use crate::btree::non_zero_to_u16;
use crate::btree::parse_btree_interior_cell_page_id;
use crate::btree::parse_btree_table_leaf_cell;
use crate::btree::set_u16;
use crate::btree::write_leaf_cell;
use crate::btree::BtreeContext;
use crate::btree::BtreePageHeader;
use crate::btree::BtreePageHeaderMut;
use crate::btree::BtreePageType;
use crate::btree::FileCorrupt;
use crate::btree::IndexCellKeyParser;
use crate::btree::PayloadInfo;
use crate::btree::TableCellKeyParser;
use crate::btree::BTREE_OVERFLOW_PAGE_ID_BYTES;
use crate::btree::BTREE_PAGE_CELL_POINTER_SIZE;
use crate::pager::swap_page_buffer;
use crate::pager::Error as PagerError;
use crate::pager::MemPage;
use crate::pager::PageBuffer;
use crate::pager::PageId;
use crate::pager::Pager;
use crate::payload::Payload;
use crate::payload::PayloadSize;
use crate::record::compare_record;
use crate::utils::i64_to_u64;
use crate::utils::len_varint_buffer;
use crate::utils::put_varint;
use crate::value::ValueCmp;

#[derive(Debug)]
pub enum Error {
    FileCorrupt { page_id: PageId, e: FileCorrupt },
    Pager { page_id: PageId, e: PagerError },
    AllocatePage(PagerError),
    NotTable,
    NotIndex,
    NotInitialized,
    Record(anyhow::Error),
    LoadPayload,
    IndexExists,
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::FileCorrupt { e, .. } => Some(e),
            Self::Pager { e, .. } => Some(e),
            Self::AllocatePage(e) => Some(e),
            Self::NotTable => None,
            Self::NotIndex => None,
            Self::NotInitialized => None,
            Self::Record(e) => e.source(),
            Self::LoadPayload => None,
            Self::IndexExists => None,
        }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FileCorrupt { page_id, e } => {
                f.write_fmt(format_args!("btree(page_id: {}): {}", page_id.get(), e))
            }
            Self::Pager { page_id, e } => {
                f.write_fmt(format_args!("pager(page_id: {}): {}", page_id.get(), e))
            }
            Self::AllocatePage(e) => f.write_fmt(format_args!("allocate new page: {e}")),
            Self::NotTable => f.write_str("not a table page"),
            Self::NotIndex => f.write_str("not an index page"),
            Self::NotInitialized => f.write_str("cursor is not initialized"),
            Self::Record(e) => f.write_fmt(format_args!("record: {}", e)),
            Self::LoadPayload => f.write_str("failed to load payload"),
            Self::IndexExists => f.write_str("index already exists"),
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct BtreePayload<'a> {
    pager: &'a Pager,
    bctx: &'a BtreeContext,
    local_page_id: PageId,
    local_payload_buffer: PageBuffer<'a>,
    payload_info: PayloadInfo,
}

impl<'a> Payload<Error> for BtreePayload<'a> {
    /// The size of the payload.
    fn size(&self) -> PayloadSize {
        self.payload_info.payload_size
    }

    /// The local payload.
    ///
    /// This may not be the entire payload if there is overflow page.
    fn buf(&self) -> &[u8] {
        &self.local_payload_buffer[self.payload_info.local_range.clone()]
    }

    /// Load the payload into the buffer.
    ///
    /// Returns the number of bytes loaded.
    ///
    /// The offset must be less than the size of the payload.
    fn load(&self, offset: usize, buf: &mut [u8]) -> Result<usize> {
        assert!(offset <= self.payload_info.payload_size.get() as usize);
        let mut n_loaded = 0;
        let mut offset = offset;
        let mut buf = buf;
        let payload = &self.local_payload_buffer[self.payload_info.local_range.clone()];

        if offset < payload.len() {
            let local_offset = offset;
            let n = std::cmp::min(payload.len() - local_offset, buf.len());
            // TODO: std::ptr::copy_nonoverlapping
            buf[..n].copy_from_slice(&payload[local_offset..local_offset + n]);
            n_loaded += n;
            offset += n;
            buf = &mut buf[n..];
        }

        let mut cur = payload.len();
        let mut overflow = self.payload_info.overflow;
        while !buf.is_empty() && cur < self.payload_info.payload_size.get() as usize {
            let overflow_page = overflow.ok_or_else(|| Error::FileCorrupt {
                page_id: self.local_page_id,
                e: FileCorrupt::new("no overflow page"),
            })?;
            let page = self
                .pager
                .get_page(overflow_page.page_id())
                .map_err(|e| Error::Pager {
                    page_id: overflow_page.page_id(),
                    e,
                })?;
            let buffer = page.buffer();
            let (payload, next_overflow) =
                overflow_page
                    .parse(self.bctx, &buffer)
                    .map_err(|e| Error::FileCorrupt {
                        page_id: overflow_page.page_id(),
                        e,
                    })?;
            if offset < cur + payload.len() {
                let local_offset = offset - cur;
                let n = std::cmp::min(payload.len() - local_offset, buf.len());
                // TODO: std::ptr::copy_nonoverlapping
                buf[..n].copy_from_slice(&payload[local_offset..local_offset + n]);
                n_loaded += n;
                offset += n;
                buf = &mut buf[n..];
            }
            cur += payload.len();
            overflow = next_overflow;
        }

        Ok(n_loaded)
    }
}

struct CursorPage {
    /// TODO: This is only for error debug message.
    page_id: PageId,
    mem: MemPage,
    idx_cell: u16,
    n_cells: u16,
    page_type: BtreePageType,
}

impl CursorPage {
    fn new(page_id: PageId, mem: MemPage) -> Self {
        let buffer = mem.buffer();
        let page_header = BtreePageHeader::from_page(&mem, &buffer);
        let n_cells = page_header.n_cells();
        let page_type = page_header.page_type();
        drop(buffer);
        Self {
            page_id,
            mem,
            idx_cell: 0,
            n_cells,
            page_type,
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
    ) -> Result<Self> {
        let mem = pager.get_page(root_page_id).map_err(|e| Error::Pager {
            page_id: root_page_id,
            e,
        })?;
        let page = CursorPage::new(root_page_id, mem);
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
    pub fn table_move_to(&mut self, key: i64) -> Result<Option<i64>> {
        // TODO: optimize for sequential access. i.e. key == previouse key + 1
        self.move_to_root();
        loop {
            if !self.current_page.page_type.is_table() {
                return Err(Error::NotTable);
            }
            let mut i_min = 0;
            let mut i_max = self.current_page.n_cells as usize;
            let buffer = self.current_page.mem.buffer();
            let cell_key_parser = TableCellKeyParser::new(&self.current_page.mem, &buffer);

            let mut max_cell_key = None;
            while i_min < i_max {
                let i_mid = (i_min + i_max) / 2;
                let cell_key =
                    cell_key_parser
                        .get_cell_key(i_mid as u16)
                        .map_err(|e| Error::FileCorrupt {
                            page_id: self.current_page.page_id,
                            e,
                        })?;
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
            if self.current_page.page_type.is_leaf() {
                self.initialized = true;
                return Ok(max_cell_key);
            }

            drop(buffer);
            self.move_to_current_child()?;
        }
    }

    /// Move to the specified btree index cell with the key.
    ///
    /// Returns `true` if exact key is found.
    ///
    /// If it does not exist, move to the next cell and returns `false`.
    pub fn index_move_to(&mut self, comparators: &[Option<ValueCmp>]) -> Result<bool> {
        let found = self.index_move_to_leaf(comparators)?;
        if !found && self.current_page.page_type.is_leaf() {
            // If the key is between the last key of the index leaf page and the parent key,
            // we need to adjust the cursor to the parent cell.
            if self.current_page.idx_cell == self.current_page.n_cells {
                while self.back_to_parent()
                    && self.current_page.idx_cell == self.current_page.n_cells
                {}
            }
        }
        Ok(found)
    }

    /// Move to the specified btree index cell with the key without adjustment.
    ///
    /// Returns `true` if exact key is found.
    ///
    /// If it does not exist, the cursor points to a cell (or tail) of a leaf
    /// page and returns `false`.
    fn index_move_to_leaf(&mut self, comparators: &[Option<ValueCmp>]) -> Result<bool> {
        self.move_to_root();
        loop {
            if !self.current_page.page_type.is_index() {
                return Err(Error::NotIndex);
            }
            let mut i_min = 0;
            let mut i_max = self.current_page.n_cells as usize;
            let buffer = self.current_page.mem.buffer();
            let cell_key_parser =
                IndexCellKeyParser::new(self.btree_ctx, &self.current_page.mem, &buffer);

            while i_min < i_max {
                let i_mid = (i_min + i_max) / 2;
                let payload_info =
                    cell_key_parser
                        .get_cell_key(i_mid as u16)
                        .map_err(|e| Error::FileCorrupt {
                            page_id: self.current_page.page_id,
                            e,
                        })?;
                let key_payload = BtreePayload {
                    pager: self.pager,
                    bctx: self.btree_ctx,
                    local_page_id: self.current_page.page_id,
                    local_payload_buffer: self.current_page.mem.buffer(),
                    payload_info,
                };
                match compare_record(comparators, &key_payload).map_err(Error::Record)? {
                    Ordering::Less => {
                        i_max = i_mid;
                    }
                    Ordering::Equal => {
                        self.current_page.idx_cell = i_mid as u16;
                        self.initialized = true;
                        return Ok(true);
                    }
                    Ordering::Greater => {
                        i_min = i_mid + 1;
                    }
                }
            }
            self.current_page.idx_cell = i_min as u16;
            if self.current_page.page_type.is_leaf() {
                self.initialized = true;
                return Ok(false);
            }

            drop(buffer);
            self.move_to_current_child()?;
        }
    }

    pub fn move_to_first(&mut self) -> Result<()> {
        self.move_to_root();
        self.current_page.idx_cell = 0;
        if !self.current_page.page_type.is_leaf() {
            self.move_to_left_most()?;
        }
        self.initialized = true;
        Ok(())
    }

    pub fn move_to_last(&mut self) -> Result<()> {
        self.move_to_root();
        if self.current_page.n_cells == 0 {
            self.current_page.idx_cell = 0;
        } else {
            while !self.current_page.page_type.is_leaf() {
                let page_id = BtreePageHeader::from_page(
                    &self.current_page.mem,
                    &self.current_page.mem.buffer(),
                )
                .right_page_id()
                .map_err(|e| Error::FileCorrupt {
                    page_id: self.current_page.page_id,
                    e,
                })?;
                self.move_to_child(page_id)?;
            }
            self.current_page.idx_cell = self.current_page.n_cells - 1;
        }
        self.initialized = true;
        Ok(())
    }

    pub fn move_next(&mut self) -> Result<()> {
        if !self.initialized {
            return Err(Error::NotInitialized);
        } else if self.parent_pages.is_empty()
            && (self.current_page.idx_cell == self.current_page.n_cells + 1
                || self.current_page.n_cells == 0)
        {
            // The cursor is completed.
            return Ok(());
        }

        self.current_page.idx_cell += 1;
        if self.current_page.page_type.is_leaf()
            && self.current_page.idx_cell < self.current_page.n_cells
        {
            return Ok(());
        }

        if self.current_page.page_type.is_table() {
            // table page never stops in the middle of the interior page.
            assert!(self.current_page.page_type.is_leaf());
            assert!(self.current_page.idx_cell == self.current_page.n_cells);
            loop {
                if !self.back_to_parent() {
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
            if !self.current_page.page_type.is_leaf()
                && self.current_page.idx_cell <= self.current_page.n_cells
            {
                assert!(self.move_to_left_most()?);
            } else {
                assert!(
                    self.current_page.page_type.is_leaf()
                        && self.current_page.idx_cell == self.current_page.n_cells
                );
                loop {
                    if self.back_to_parent() {
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
            return Err(Error::FileCorrupt {
                page_id: self.current_page.page_id,
                e: FileCorrupt::new("btree page type is invalid"),
            });
        }
        Ok(())
    }

    /// Insert a new key to index.
    ///
    /// This fails if the key already exists. If you need to update the key for
    /// an entry, delete the key in the index first.
    pub fn index_insert<P: Payload<()>>(
        &mut self,
        comparators: &[Option<ValueCmp>],
        payload: &P,
    ) -> Result<()> {
        if self.index_move_to_leaf(comparators)? {
            // index_insert() does not support updating a key.
            return Err(Error::IndexExists);
        }

        assert!(self.current_page.page_type.is_index());
        // Since the key is not in the index, the cursor must be pointing the leaf page.
        assert!(self.current_page.page_type.is_leaf());

        let mut cell_header_buf = [0; 9];

        let (cell_header, n_local, overflow_page_id) =
            self.pack_cell(cell_header_buf.as_mut_slice(), payload, None)?;

        self.insert_cell(cell_header, payload, n_local, overflow_page_id)
    }

    /// Insert or update a new item to the table.
    ///
    /// There should not be other [BtreeCursor]s pointing the same btree.
    /// Otherwise, this fails.
    pub fn table_insert<P: Payload<()>>(&mut self, key: i64, payload: &P) -> Result<()> {
        let current_cell_key = self.table_move_to(key)?;

        assert!(self.current_page.page_type.is_table());
        assert!(self.current_page.page_type.is_leaf());

        if let Some(current_cell_key) = current_cell_key {
            if current_cell_key == key {
                // TODO: Update the payload
                todo!("update the payload");
            }
        }

        let mut cell_header_buf = [0; 18];

        let (cell_header, n_local, overflow_page_id) =
            self.pack_cell(cell_header_buf.as_mut_slice(), payload, Some(key))?;

        self.insert_cell(cell_header, payload, n_local, overflow_page_id)
    }

    fn pack_cell<'b, P: Payload<()>>(
        &self,
        cell_header_buf: &'b mut [u8],
        payload: &P,
        table_key: Option<i64>,
    ) -> Result<(&'b [u8], u16, Option<PageId>)> {
        assert!(cell_header_buf.len() >= 9);
        let mut cell_header_size = put_varint(cell_header_buf, payload.size().get() as u64) as u16;
        if let Some(key) = table_key {
            assert!(cell_header_buf.len() >= 18);
            cell_header_size += put_varint(
                &mut cell_header_buf[cell_header_size as usize..],
                i64_to_u64(key),
            ) as u16;
        }
        let cell_header = &cell_header_buf[..cell_header_size as usize];

        let is_table = table_key.is_some();
        if payload.size().get() <= self.btree_ctx.max_local(is_table) as u32 {
            Ok((cell_header, payload.size().get() as u16, None))
        } else {
            // Split the payload into local and overflow pages.
            let n_local = self.btree_ctx.n_local(is_table, payload.size());
            let mut i_overflow_payload = n_local as usize;
            let usable_size_overflow =
                self.btree_ctx.usable_size as usize - BTREE_OVERFLOW_PAGE_ID_BYTES;
            let (first_overflow_page_id, mut page) =
                self.pager.allocate_page().map_err(Error::AllocatePage)?;
            let mut page_id = first_overflow_page_id;
            while i_overflow_payload + usable_size_overflow < payload.size().get() as usize {
                let (next_page_id, next_page) =
                    self.pager.allocate_page().map_err(Error::AllocatePage)?;
                // make_page_mut() must succeed for allocated pages.
                let mut buffer = self.pager.make_page_mut(&page).unwrap();
                let next_page_id_buf = next_page_id.get().to_be_bytes();
                buffer[..next_page_id_buf.len()].copy_from_slice(&next_page_id_buf);
                let n = payload
                    .load(
                        i_overflow_payload,
                        &mut buffer[next_page_id_buf.len()..self.btree_ctx.usable_size as usize],
                    )
                    .map_err(|_| Error::LoadPayload)?;
                assert_eq!(n, usable_size_overflow);
                drop(buffer);
                i_overflow_payload += usable_size_overflow;
                page_id = next_page_id;
                page = next_page;
            }
            let mut buffer = self
                .pager
                .make_page_mut(&page)
                .map_err(|e| Error::Pager { page_id, e })?;
            let last_overflow_size = payload.size().get() as usize - i_overflow_payload;
            buffer[..BTREE_OVERFLOW_PAGE_ID_BYTES].fill(0);
            let n = payload
                .load(
                    i_overflow_payload,
                    &mut buffer[BTREE_OVERFLOW_PAGE_ID_BYTES
                        ..BTREE_OVERFLOW_PAGE_ID_BYTES + last_overflow_size],
                )
                .map_err(|_| Error::LoadPayload)?;
            assert_eq!(n, last_overflow_size);
            drop(buffer);

            Ok((cell_header, n_local, Some(first_overflow_page_id)))
        }
    }

    fn insert_cell<P: Payload<()>>(
        &mut self,
        cell_header: &[u8],
        payload: &P,
        n_local: u16,
        overflow_page_id: Option<PageId>,
    ) -> Result<()> {
        let new_cell_size = cell_header.len()
            + n_local as usize
            + BTREE_OVERFLOW_PAGE_ID_BYTES * overflow_page_id.is_some() as usize;
        assert!(new_cell_size <= u16::MAX as usize);
        // Allocate 4 bytes or more to be compatible to allocateSpace() of SQLite.
        // Otherwise freeSpace() of SQLite corrupts the database file (e.g. on updating
        // or deleting records). 4 bytes allocation is introduced in order to make
        // spaces easier to reused as freeblock. 1 ~ 3 bytes spaces are counted as
        // fragmented and never reused. cell_size can be less than 4 on index pages.
        let mut new_cell_size = if new_cell_size < 4 {
            4
        } else {
            new_cell_size as u16
        };

        let mut depth = self.parent_pages.len();
        let mut interior_cell_buf = self.pager.allocate_tmp_page();
        // sub interior cell is for a special case when table leaf page is splitted into 3 pages.
        // In that case, new 2 interior cells are inserted to the parent page.
        let mut sub_interiror_cell_buf = [0; 13];
        let mut sub_interior_cell_len = None;
        // This is used to update idx_cell of the parent page when splitting a child page.
        let mut new_cell_in_right_page = false;

        loop {
            let current_page = if depth == self.parent_pages.len() {
                &mut self.current_page
            } else {
                &mut self.parent_pages[depth]
            };

            // make_page_mut() should succeed because there must be no buffer reference of
            // the page. We can guarantee it because:
            //
            // * This cursor is the only cursor handling the btree containing the page and
            // * Only the possible reference is the returned payload from
            //   get_table_payload(). However the payload is dropped before calling insert()
            //   which is mutable method.
            let mut buffer =
                self.pager
                    .make_page_mut(&current_page.mem)
                    .map_err(|e| Error::Pager {
                        page_id: current_page.page_id,
                        e,
                    })?;

            // TODO: Cache free size.
            let free_size = compute_free_size(&current_page.mem, &buffer, current_page.n_cells)
                .map_err(|e| Error::FileCorrupt {
                    page_id: current_page.page_id,
                    e,
                })?;

            if free_size >= new_cell_size + 2 {
                let page_header = BtreePageHeader::from_page_mut(&current_page.mem, &buffer);
                let page_type = current_page.page_type;
                let header_size = page_type.header_size();
                let first_freeblock_offset = page_header.first_freeblock_offset();
                let cell_content_area_offset =
                    page_header.cell_content_area_offset().get() as usize;
                let unallocated_space_offset =
                    cell_pointer_offset(&current_page.mem, current_page.n_cells, header_size);
                let fragmented_free_bytes = page_header.fragmented_free_bytes();
                // unallocated_size must fit in u16 because cell_content_area_offset is at most
                // 65536 and unallocated_space_offset must be bigger than 0.
                // cell_content_area_offset < unallocated_space_offset is asserted in
                // compute_free_size().
                let unallocated_size = (cell_content_area_offset - unallocated_space_offset) as u16;

                // Allocate space
                //
                // 1. Search freeblock first.
                // 2. Defragmentation if needed.
                // 3. Allocate space from unallocated space.
                let allocated_offset = {
                    // Search freeblock first.
                    let allocated_offset = if unallocated_size >= 2
                    && first_freeblock_offset != 0
                    // Total fragments may not exceed 60 bytes. Otherwise Give up seeking freeblocks
                    // and try defragmentation.
                    && fragmented_free_bytes <= 57
                    {
                        allocate_from_freeblocks(
                            &current_page.mem,
                            &mut buffer,
                            first_freeblock_offset,
                            new_cell_size,
                        )
                    } else {
                        None
                    };

                    if let Some(offset) = allocated_offset {
                        // 1. Allocated from freeblock.
                        offset
                    } else {
                        // 2. Defragmentation if needed.
                        let mut cell_content_area_offset = cell_content_area_offset;
                        if unallocated_size < new_cell_size + 2 {
                            // TODO: Optimization: Move cell block of the size of a freeblock if
                            // there is only a few freeblocks. See defragmentPage() of SQLite.
                            let mut tmp_page = self.pager.allocate_tmp_page();
                            buffer.swap_tmp(&mut tmp_page);
                            // Copy database header if the page is page 1.
                            buffer[..current_page.mem.header_offset]
                                .copy_from_slice(&tmp_page[..current_page.mem.header_offset]);
                            let mut page_header =
                                BtreePageHeaderMut::from_page(&current_page.mem, &mut buffer);
                            page_header.set_page_type(current_page.page_type);
                            page_header.set_first_freeblock_offset(0);
                            page_header.clear_fragmented_free_bytes();
                            if !current_page.page_type.is_leaf() {
                                let right_page_id_offset = current_page.mem.header_offset + 8;
                                buffer[right_page_id_offset..right_page_id_offset + 4]
                                    .copy_from_slice(
                                        &tmp_page[right_page_id_offset..right_page_id_offset + 4],
                                    );
                            }
                            // cell_content_area_offset and n_cells will be set later.
                            cell_content_area_offset = self.btree_ctx.usable_size as usize;
                            // Copy reserved area.
                            buffer[cell_content_area_offset..]
                                .copy_from_slice(&tmp_page[cell_content_area_offset..]);
                            let compute_cell_size = page_type.compute_cell_size_fn();
                            for i in 0..current_page.n_cells {
                                let offset =
                                    get_cell_offset(&current_page.mem, &tmp_page, i, header_size)
                                        .map_err(|e| Error::FileCorrupt {
                                        page_id: current_page.page_id,
                                        e,
                                    })?;
                                let cell_size =
                                    compute_cell_size(self.btree_ctx, &tmp_page, offset).map_err(
                                        |e| Error::FileCorrupt {
                                            page_id: current_page.page_id,
                                            e,
                                        },
                                    )?;
                                // There must be enough size of unallocated space before
                                // cell_content_area_offset because all cells have fit in the page
                                // before defragmentation.
                                let new_cell_content_area_offset = allocate_from_unallocated_space(
                                    &current_page.mem,
                                    &mut buffer,
                                    header_size,
                                    cell_content_area_offset,
                                    i,
                                    cell_size,
                                );
                                buffer[new_cell_content_area_offset..cell_content_area_offset]
                                    .copy_from_slice(
                                        &tmp_page[offset..offset + cell_size as usize],
                                    );
                                cell_content_area_offset = new_cell_content_area_offset;
                            }
                            // unallocated_space_offset does not change because n_cell is not
                            // changed.
                            assert!(
                                unallocated_space_offset + 2
                                    <= cell_content_area_offset - new_cell_size as usize
                            );
                            // Clear the unallocated space.
                            buffer[unallocated_space_offset + 2
                                ..cell_content_area_offset - new_cell_size as usize]
                                .fill(0);
                        }

                        // 3. Allocate space from unallocated space.
                        let allocated_offset = cell_content_area_offset - new_cell_size as usize;
                        // cell_content_area_offset is less than or equal to 65536. data is not
                        // empty. The offset must be less than 65536 and
                        // safe to cast into u16.
                        assert!(allocated_offset <= u16::MAX as usize);

                        // New cell content area offset must not be less than the tail of cell
                        // pointers.
                        assert!(allocated_offset >= unallocated_space_offset + 2);
                        BtreePageHeaderMut::from_page(&current_page.mem, &mut buffer)
                            .set_cell_content_area_offset(allocated_offset as u16);
                        allocated_offset
                    }
                };

                current_page.n_cells += 1;
                BtreePageHeaderMut::from_page(&current_page.mem, &mut buffer)
                    .set_n_cells(current_page.n_cells);

                // Update cell pointer.
                let cell_pointer_offset =
                    cell_pointer_offset(&current_page.mem, current_page.idx_cell, header_size);
                // Insert the new cell between cells. If the pointer is at the tail, this copy
                // is no-op.
                buffer.copy_within(
                    cell_pointer_offset..unallocated_space_offset,
                    cell_pointer_offset + 2,
                );
                set_u16(&mut buffer, cell_pointer_offset, allocated_offset as u16);

                if page_type.is_leaf() {
                    write_leaf_cell(
                        &mut buffer,
                        allocated_offset,
                        cell_header,
                        payload,
                        n_local,
                        overflow_page_id,
                    );
                } else {
                    current_page.idx_cell += new_cell_in_right_page as u16;
                    buffer[allocated_offset..allocated_offset + new_cell_size as usize]
                        .copy_from_slice(&interior_cell_buf[..new_cell_size as usize]);
                }
                if let Some(sub_interior_cell_len) = sub_interior_cell_len.take() {
                    new_cell_size = sub_interior_cell_len;
                    interior_cell_buf[..new_cell_size as usize]
                        .copy_from_slice(&sub_interiror_cell_buf[..new_cell_size as usize]);
                    continue;
                }
                return Ok(());
            }

            // Split the overflowing page.
            if depth == 0 {
                let (page_id, new_page) =
                    self.pager.allocate_page().map_err(Error::AllocatePage)?;
                // make_page_mut() must succeed for allocated pages.
                let mut new_buffer = self.pager.make_page_mut(&new_page).unwrap();
                swap_page_buffer(&mut buffer, &mut new_buffer);
                // Build the btree page header of the root page.
                let mut page_header = BtreePageHeaderMut::from_page(&current_page.mem, &mut buffer);
                let root_page_type = current_page.page_type.interior_type();
                page_header.set_page_type(root_page_type);
                page_header.set_first_freeblock_offset(0);
                page_header.set_n_cells(0);
                page_header
                    .set_cell_content_area_offset(non_zero_to_u16(self.btree_ctx.usable_size));
                page_header.clear_fragmented_free_bytes();
                page_header.set_right_page_id(page_id);
                if current_page.mem.header_offset > 0 {
                    // Move database header back to page 1.
                    buffer[..current_page.mem.header_offset]
                        .copy_from_slice(&new_buffer[..current_page.mem.header_offset]);
                    // Move the page header and cell pointers starting after the database
                    // header to head of the page. Values does not change because they are
                    // independent from the position of page header.
                    new_buffer.copy_within(
                        current_page.mem.header_offset
                            ..current_page.mem.header_offset
                                + current_page.page_type.header_size() as usize
                                + 2 * current_page.n_cells as usize,
                        0,
                    );
                    // TODO: Increase cached free size by the size of
                    // database header.
                }
                drop(buffer);
                drop(new_buffer);
                let mut new_page = new_page;
                std::mem::swap(&mut current_page.mem, &mut new_page);
                self.parent_pages.insert(
                    0,
                    CursorPage {
                        page_id,
                        mem: new_page,
                        idx_cell: 0,
                        n_cells: 0,
                        page_type: root_page_type,
                    },
                );
                depth += 1;
            } else {
                let header_size = current_page.page_type.header_size();

                const CELL_POINTER_SIZE: u32 = BTREE_PAGE_CELL_POINTER_SIZE as u32;
                // total_size is u32 because it may overflow u16 size.
                let mut total_size =
                    new_cell_size as u32 + CELL_POINTER_SIZE * (current_page.n_cells as u32 + 1);
                let mut cells = Vec::with_capacity(current_page.n_cells as usize);
                let compute_cell_size = current_page.page_type.compute_cell_size_fn();
                for i in 0..current_page.n_cells {
                    let offset = get_cell_offset(&current_page.mem, &buffer, i, header_size)
                        .map_err(|e| Error::FileCorrupt {
                            page_id: current_page.page_id,
                            e,
                        })?;
                    let cell_size =
                        compute_cell_size(self.btree_ctx, &buffer, offset).map_err(|e| {
                            Error::FileCorrupt {
                                page_id: current_page.page_id,
                                e,
                            }
                        })?;
                    cells.push((offset, cell_size));
                    total_size += cell_size as u32;
                }
                let mut left_size: u32 = 0;
                let mut right_size: u32 = total_size;
                let mut i_right = None;
                for i in 0..current_page.idx_cell {
                    left_size += cells[i as usize].1 as u32 + CELL_POINTER_SIZE;
                    right_size -= cells[i as usize].1 as u32 + CELL_POINTER_SIZE;
                    // left_size is guaranteed to be fit in a page because the cells were present in
                    // the overflowing page.
                    if left_size >= right_size {
                        i_right = Some(i + 1);
                        break;
                    }
                }
                let (move_to_right, split_into_3, idx_cells) = if let Some(i_right) = i_right {
                    // Move right half of cells and the new cell to a new page.
                    (true, false, i_right..current_page.n_cells)
                } else {
                    let capacity = self.btree_ctx.usable_size - header_size as u32;
                    left_size += new_cell_size as u32 + CELL_POINTER_SIZE;
                    if left_size > capacity {
                        if right_size > capacity {
                            // Split into 3 pages.
                            // The page must not be a table interior page because a cell is at most
                            // 13 bytes.
                            // The page must not be a index pages because a cell is at most about
                            // quarter of usable size.
                            assert!(current_page.page_type.is_table_leaf());
                        } else {
                            // If idx_cell is zero, left_size is the same as the new cell size. But
                            // the new cell size must not exceeds the capacity. So idx_cell must be
                            // more than zero.
                            assert_ne!(current_page.idx_cell, 0);
                        }
                        // Move right cells to a new page.
                        (
                            true,
                            right_size > capacity,
                            current_page.idx_cell..current_page.n_cells,
                        )
                    } else {
                        right_size -= new_cell_size as u32 + CELL_POINTER_SIZE;
                        let mut i_right = current_page.n_cells;
                        for i in current_page.idx_cell..current_page.n_cells {
                            if left_size >= right_size {
                                i_right = i;
                                break;
                            }
                            left_size += cells[i as usize].1 as u32 + CELL_POINTER_SIZE;
                            if left_size > capacity {
                                i_right = i;
                                break;
                            }
                            right_size -= cells[i as usize].1 as u32 + CELL_POINTER_SIZE;
                        }

                        // Move remaining cell pointers
                        buffer.copy_within(
                            cell_pointer_offset(&current_page.mem, i_right, header_size)
                                ..cell_pointer_offset(
                                    &current_page.mem,
                                    current_page.n_cells,
                                    header_size,
                                ),
                            cell_pointer_offset(&current_page.mem, 0, header_size),
                        );
                        // Move left half of cells to a new page.
                        (false, false, 0..i_right)
                    }
                };
                assert!(current_page.idx_cell >= idx_cells.start);
                assert!(current_page.idx_cell <= idx_cells.end);
                let new_idx_cell = current_page.idx_cell - idx_cells.start;

                let mut i_new = 0;
                let n_moved_cells = idx_cells.len() as u16;
                let n_new_cells = n_moved_cells
                    + (!split_into_3) as u16
                    + (!split_into_3 && sub_interior_cell_len.is_some()) as u16;
                let mut first_freeblock_offset =
                    BtreePageHeader::from_page_mut(&current_page.mem, &buffer)
                        .first_freeblock_offset();
                // TODO: Does this assertion avoid boundary check of cells[i as usize]?
                assert!(idx_cells.end as usize <= cells.len());

                let (new_page_id, new_page) =
                    self.pager.allocate_page().map_err(Error::AllocatePage)?;
                // make_page_mut() must succeed for allocated pages.
                let mut new_buffer = self.pager.make_page_mut(&new_page).unwrap();
                let mut cell_content_area_offset = self.btree_ctx.usable_size as usize;
                // Move cells to the new page.
                for i_current in idx_cells.clone() {
                    if i_current == current_page.idx_cell && !split_into_3 {
                        i_new += 1 + sub_interior_cell_len.is_some() as u16;
                    }
                    let (offset, cell_size) = cells[i_current as usize];
                    let new_cell_content_area_offset = allocate_from_unallocated_space(
                        &new_page,
                        &mut new_buffer,
                        header_size,
                        cell_content_area_offset,
                        i_new,
                        cell_size,
                    );
                    new_buffer[new_cell_content_area_offset..cell_content_area_offset]
                        .copy_from_slice(&buffer[offset..offset + cell_size as usize]);
                    cell_content_area_offset = new_cell_content_area_offset;
                    i_new += 1;

                    // TODO: Merge freeblock to unallocated space if possible.
                    // Put the cell to the freeblock list.
                    set_u16(&mut buffer, offset, first_freeblock_offset);
                    set_u16(&mut buffer, offset + 2, cell_size);
                    first_freeblock_offset = offset as u16;
                }

                // Insert the new cell.
                if split_into_3 {
                    let (new_page_id, new_page) =
                        self.pager.allocate_page().map_err(Error::AllocatePage)?;
                    let mut new_buffer = self.pager.make_page_mut(&new_page).unwrap();

                    let cell_content_area_offset = allocate_from_unallocated_space(
                        &new_page,
                        &mut new_buffer,
                        header_size,
                        self.btree_ctx.usable_size as usize,
                        0,
                        new_cell_size,
                    );
                    assert!(current_page.page_type.is_leaf());
                    write_leaf_cell(
                        &mut new_buffer,
                        cell_content_area_offset,
                        cell_header,
                        payload,
                        n_local,
                        overflow_page_id,
                    );

                    let mut new_page_header =
                        BtreePageHeaderMut::from_page(&new_page, &mut new_buffer);
                    new_page_header.set_page_type(current_page.page_type);
                    new_page_header.set_first_freeblock_offset(0);
                    new_page_header.set_n_cells(1);
                    // At least 1 cell is written. cell_content_area_offset must fit in u16.
                    new_page_header.set_cell_content_area_offset(cell_content_area_offset as u16);
                    new_page_header.clear_fragmented_free_bytes();

                    sub_interiror_cell_buf[..4].copy_from_slice(&new_page_id.get().to_be_bytes());
                    let payload_size_len = len_varint_buffer(
                        &new_buffer[cell_content_area_offset..],
                    )
                    .ok_or_else(|| Error::FileCorrupt {
                        page_id: new_page_id,
                        e: FileCorrupt::new("payload size len"),
                    })?;
                    let key_offset = cell_content_area_offset + payload_size_len;
                    let key_len =
                        len_varint_buffer(&new_buffer[key_offset..]).ok_or_else(|| {
                            Error::FileCorrupt {
                                page_id: new_page_id,
                                e: FileCorrupt::new("key length"),
                            }
                        })?;
                    sub_interiror_cell_buf[4..4 + key_len]
                        .copy_from_slice(&new_buffer[key_offset..key_offset + key_len]);
                    sub_interior_cell_len = Some(4 + key_len as u16);

                    drop(new_buffer);
                } else {
                    cell_content_area_offset = allocate_from_unallocated_space(
                        &new_page,
                        &mut new_buffer,
                        header_size,
                        cell_content_area_offset,
                        current_page.idx_cell - idx_cells.start,
                        new_cell_size,
                    );
                    if current_page.page_type.is_leaf() {
                        write_leaf_cell(
                            &mut new_buffer,
                            cell_content_area_offset,
                            cell_header,
                            payload,
                            n_local,
                            overflow_page_id,
                        );
                    } else {
                        new_buffer[cell_content_area_offset
                            ..cell_content_area_offset + new_cell_size as usize]
                            .copy_from_slice(&interior_cell_buf[..new_cell_size as usize]);
                        if let Some(sub_interior_cell_len) = sub_interior_cell_len.take() {
                            cell_content_area_offset = allocate_from_unallocated_space(
                                &new_page,
                                &mut new_buffer,
                                header_size,
                                cell_content_area_offset,
                                current_page.idx_cell + 1 - idx_cells.start,
                                new_cell_size,
                            );
                            new_buffer[cell_content_area_offset
                                ..cell_content_area_offset + sub_interior_cell_len as usize]
                                .copy_from_slice(
                                    &sub_interiror_cell_buf[..sub_interior_cell_len as usize],
                                );
                        }
                    }
                };

                let mut page_header = BtreePageHeaderMut::from_page(&current_page.mem, &mut buffer);
                page_header.set_first_freeblock_offset(first_freeblock_offset);
                let n_current_cells = current_page.n_cells - n_moved_cells;
                page_header.set_n_cells(n_current_cells);

                let mut new_page_header = BtreePageHeaderMut::from_page(&new_page, &mut new_buffer);
                new_page_header.set_page_type(current_page.page_type);
                new_page_header.set_first_freeblock_offset(0);
                new_page_header.set_n_cells(n_new_cells);
                // At least 1 cell is written. cell_content_area_offset must fit in u16.
                new_page_header.set_cell_content_area_offset(cell_content_area_offset as u16);
                new_page_header.clear_fragmented_free_bytes();

                let n_left_cells = if move_to_right {
                    if !current_page.page_type.is_leaf() {
                        // Copy the right page id from left to right page.
                        // No header offset calibration because both pages must not page 1
                        // because they are not the root page.
                        new_buffer[8..12].copy_from_slice(&buffer[8..12]);
                    }
                    // The parent interior page points at the current_page as a right page.
                    swap_page_buffer(&mut buffer, &mut new_buffer);
                    n_current_cells
                } else {
                    n_new_cells
                };
                // Now new_buffer points at the left page.
                let mut left_buffer = new_buffer;

                // Fill interior cell with the new key.
                let cell_offset = get_cell_offset(
                    &current_page.mem,
                    &left_buffer,
                    n_left_cells - 1,
                    header_size,
                )
                .map_err(|e| Error::FileCorrupt {
                    page_id: current_page.page_id,
                    e,
                })?;
                // TODO: Better way to get the range of key? Reuse the size array
                let key_range =
                    if current_page.page_type.is_leaf() {
                        if current_page.page_type.is_table() {
                            // payload_size_length
                            let key_offset_in_cell = len_varint_buffer(&left_buffer[cell_offset..])
                                .ok_or_else(|| Error::FileCorrupt {
                                    page_id: current_page.page_id,
                                    e: FileCorrupt::new("payload size len"),
                                })?;
                            let key_offset = cell_offset + key_offset_in_cell;
                            let key_length = len_varint_buffer(&left_buffer[key_offset..])
                                .ok_or_else(|| Error::FileCorrupt {
                                    page_id: current_page.page_id,
                                    e: FileCorrupt::new("key length"),
                                })?;
                            key_offset..key_offset + key_length
                        } else if current_page.page_type.is_index() {
                            let cell_size =
                                compute_cell_size(self.btree_ctx, &left_buffer, cell_offset)
                                    .map_err(|e| Error::FileCorrupt {
                                        page_id: current_page.page_id,
                                        e,
                                    })?;
                            cell_offset..cell_offset + cell_size as usize
                        } else {
                            return Err(Error::FileCorrupt {
                                page_id: current_page.page_id,
                                e: FileCorrupt::new("invalid page type"),
                            });
                        }
                    } else {
                        // Set the right page id of the left page.
                        // No header offset calibration because both pages must not page 1
                        // because they are not the root page.
                        left_buffer.copy_within(cell_offset..cell_offset + 4, 8);
                        let key_offset_in_cell = 4;
                        if current_page.page_type.is_table() {
                            let key_offset = cell_offset + key_offset_in_cell;
                            let key_length = len_varint_buffer(&left_buffer[key_offset..])
                                .ok_or_else(|| Error::FileCorrupt {
                                    page_id: current_page.page_id,
                                    e: FileCorrupt::new("key length"),
                                })?;
                            key_offset..key_offset + key_length
                        } else if current_page.page_type.is_index() {
                            let cell_size =
                                compute_cell_size(self.btree_ctx, &left_buffer, cell_offset)
                                    .map_err(|e| Error::FileCorrupt {
                                        page_id: current_page.page_id,
                                        e,
                                    })?;
                            cell_offset + 4..cell_offset + cell_size as usize
                        } else {
                            return Err(Error::FileCorrupt {
                                page_id: current_page.page_id,
                                e: FileCorrupt::new("invalid page type"),
                            });
                        }
                    };
                let key = &left_buffer[key_range];
                new_cell_size = 4 + key.len() as u16;
                interior_cell_buf[..4].copy_from_slice(&new_page_id.get().to_be_bytes());
                interior_cell_buf[4..new_cell_size as usize].copy_from_slice(key);
                let is_table_leaf = current_page.page_type.is_table_leaf();
                if !is_table_leaf {
                    // Remove the cell at the tail.
                    // TODO: add the cell to freeblocks list or try not to copy the cell.
                    BtreePageHeaderMut::from_page(&current_page.mem, &mut left_buffer)
                        .set_n_cells(n_left_cells - 1);
                }

                drop(buffer);
                drop(left_buffer);
                // The new_page contains the new cell. Note that new_buffer (left_buffer) may
                // not points at the buffer of new_page.
                current_page.mem = new_page;
                current_page.n_cells = n_new_cells;
                current_page.n_cells -= (!move_to_right && !is_table_leaf) as u16;
                current_page.idx_cell = new_idx_cell;
                new_cell_in_right_page = move_to_right;

                depth -= 1;
            }
        }
    }

    /// Delete all entries in the tree.
    ///
    /// Returns the number of entries deleted.
    pub fn clear(&mut self) -> Result<u64> {
        self.move_to_first()?;
        let mut n_deleted = 0;
        loop {
            if self.current_page.page_type.is_leaf() {
                // TODO: Delete overflow payloads.
                self.current_page.idx_cell = self.current_page.n_cells;
                while self.current_page.idx_cell == self.current_page.n_cells {
                    if self.current_page.page_type.is_leaf()
                        || self.current_page.page_type.is_index()
                    {
                        let compute_overflow_page =
                            self.current_page.page_type.compute_overflow_page_fn();
                        let buffer = self.current_page.mem.buffer();
                        let header_size = self.current_page.page_type.header_size();
                        for i in 0..self.current_page.n_cells {
                            let offset =
                                get_cell_offset(&self.current_page.mem, &buffer, i, header_size)
                                    .map_err(|e| Error::FileCorrupt {
                                        page_id: self.current_page.page_id,
                                        e,
                                    })?;
                            let mut overflow_page =
                                compute_overflow_page(self.btree_ctx, &buffer, offset).map_err(
                                    |e| Error::FileCorrupt {
                                        page_id: self.current_page.page_id,
                                        e,
                                    },
                                )?;
                            while let Some(overflow_page_unwrap) = overflow_page {
                                let next_page_id = overflow_page_unwrap.page_id();
                                let next_page = self.pager.get_page(next_page_id).map_err(|e| {
                                    Error::Pager {
                                        page_id: self.current_page.page_id,
                                        e,
                                    }
                                })?;
                                let buffer = next_page.buffer();
                                let (_, next_overflow_page) = overflow_page_unwrap
                                    .parse(self.btree_ctx, &buffer)
                                    .map_err(|e| Error::FileCorrupt {
                                        page_id: next_page_id,
                                        e,
                                    })?;
                                overflow_page = next_overflow_page;
                                drop(buffer);
                                self.pager
                                    .delete_page(next_page_id)
                                    .map_err(|e| Error::Pager {
                                        page_id: self.current_page.page_id,
                                        e,
                                    })?;
                            }
                        }
                        n_deleted += self.current_page.n_cells as u64;
                    }

                    if self.parent_pages.is_empty() {
                        let mut buffer =
                            self.pager
                                .make_page_mut(&self.current_page.mem)
                                .map_err(|e| Error::Pager {
                                    page_id: self.current_page.page_id,
                                    e,
                                })?;
                        self.current_page.page_type = self.current_page.page_type.leaf_type();
                        self.current_page.idx_cell = 0;
                        self.current_page.n_cells = 0;
                        self.initialized = true;
                        let mut page_header =
                            BtreePageHeaderMut::from_page(&self.current_page.mem, &mut buffer);
                        page_header.set_page_type(self.current_page.page_type);
                        page_header.set_first_freeblock_offset(0);
                        page_header.set_n_cells(0);
                        page_header.set_cell_content_area_offset(non_zero_to_u16(
                            self.btree_ctx.usable_size,
                        ));
                        page_header.clear_fragmented_free_bytes();
                        return Ok(n_deleted);
                    }

                    self.pager
                        .delete_page(self.current_page.page_id)
                        .map_err(|e| Error::Pager {
                            page_id: self.current_page.page_id,
                            e,
                        })?;

                    assert!(self.back_to_parent());
                }
                self.current_page.idx_cell += 1;
                assert!(!self.current_page.page_type.is_leaf());
            }

            // TODO: Delete overflow payloads.

            self.move_to_current_child()?;
        }
    }

    pub fn get_table_key(&self) -> Result<Option<i64>> {
        if !self.initialized {
            return Err(Error::NotInitialized);
        } else if !self.current_page.page_type.is_table() {
            return Err(Error::NotTable);
        } else if self.current_page.idx_cell >= self.current_page.n_cells {
            return Ok(None);
        }
        assert!(self.current_page.page_type.is_leaf());
        let buffer = self.current_page.mem.buffer();
        let cell_key_parser = TableCellKeyParser::new(&self.current_page.mem, &buffer);
        let key = cell_key_parser
            .get_cell_key(self.current_page.idx_cell)
            .map_err(|e| Error::FileCorrupt {
                page_id: self.current_page.page_id,
                e,
            })?;
        Ok(Some(key))
    }

    pub fn get_table_payload(&self) -> Result<Option<(i64, BtreePayload)>> {
        if !self.initialized {
            return Err(Error::NotInitialized);
        } else if !self.current_page.page_type.is_table() {
            return Err(Error::NotTable);
        } else if self.current_page.idx_cell >= self.current_page.n_cells {
            return Ok(None);
        }
        assert!(self.current_page.page_type.is_leaf());
        let buffer = self.current_page.mem.buffer();
        let (key, payload_info) = parse_btree_table_leaf_cell(
            self.btree_ctx,
            &self.current_page.mem,
            &buffer,
            self.current_page.idx_cell,
        )
        .map_err(|e| Error::FileCorrupt {
            page_id: self.current_page.page_id,
            e,
        })?;
        Ok(Some((
            key,
            BtreePayload {
                pager: self.pager,
                bctx: self.btree_ctx,
                local_page_id: self.current_page.page_id,
                local_payload_buffer: buffer,
                payload_info,
            },
        )))
    }

    pub fn get_index_payload(&self) -> Result<Option<BtreePayload>> {
        if !self.initialized {
            return Err(Error::NotInitialized);
        } else if !self.current_page.page_type.is_index() {
            return Err(Error::NotIndex);
        } else if self.current_page.idx_cell >= self.current_page.n_cells {
            return Ok(None);
        }
        let buffer = self.current_page.mem.buffer();
        let cell_key_parser =
            IndexCellKeyParser::new(self.btree_ctx, &self.current_page.mem, &buffer);
        let payload_info = cell_key_parser
            .get_cell_key(self.current_page.idx_cell)
            .map_err(|e| Error::FileCorrupt {
                page_id: self.current_page.page_id,
                e,
            })?;
        Ok(Some(BtreePayload {
            pager: self.pager,
            bctx: self.btree_ctx,
            local_page_id: self.current_page.page_id,
            local_payload_buffer: buffer,
            payload_info,
        }))
    }

    /// Move to the left most cell in its child and grand child page.
    ///
    /// The cursor must points to a interior page.
    /// If cursor is completed, return `Ok(false)`.
    fn move_to_left_most(&mut self) -> Result<bool> {
        assert!(!self.current_page.page_type.is_leaf());
        let buffer = self.current_page.mem.buffer();
        let page_id = match self.current_page.idx_cell.cmp(&self.current_page.n_cells) {
            Ordering::Less => parse_btree_interior_cell_page_id(
                &self.current_page.mem,
                &buffer,
                self.current_page.idx_cell,
            )
            .map_err(|e| Error::FileCorrupt {
                page_id: self.current_page.page_id,
                e,
            })?,
            Ordering::Equal => {
                let page_header = BtreePageHeader::from_page(&self.current_page.mem, &buffer);
                page_header
                    .right_page_id()
                    .map_err(|e| Error::FileCorrupt {
                        page_id: self.current_page.page_id,
                        e,
                    })?
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
            if self.current_page.page_type.is_leaf() {
                break;
            }
            let buffer = self.current_page.mem.buffer();
            let page_id = parse_btree_interior_cell_page_id(&self.current_page.mem, &buffer, 0)
                .map_err(|e| Error::FileCorrupt {
                    page_id: self.current_page.page_id,
                    e,
                })?;
            drop(buffer);
            self.move_to_child(page_id)?;
        }
        Ok(true)
    }

    fn move_to_root(&mut self) {
        if !self.parent_pages.is_empty() {
            self.parent_pages.truncate(1);
            self.current_page = self.parent_pages.pop().unwrap();
        }
    }

    fn move_to_child(&mut self, page_id: PageId) -> Result<()> {
        let mem = self
            .pager
            .get_page(page_id)
            .map_err(|e| Error::Pager { page_id, e })?;
        let mut page = CursorPage::new(page_id, mem);
        std::mem::swap(&mut self.current_page, &mut page);
        self.parent_pages.push(page);
        Ok(())
    }

    fn move_to_current_child(&mut self) -> Result<()> {
        let buffer = self.current_page.mem.buffer();
        let next_page_id = if self.current_page.idx_cell == self.current_page.n_cells {
            BtreePageHeader::from_page(&self.current_page.mem, &buffer)
                .right_page_id()
                .map_err(|e| Error::FileCorrupt {
                    page_id: self.current_page.page_id,
                    e,
                })?
        } else {
            parse_btree_interior_cell_page_id(
                &self.current_page.mem,
                &buffer,
                self.current_page.idx_cell,
            )
            .map_err(|e| Error::FileCorrupt {
                page_id: self.current_page.page_id,
                e,
            })?
        };
        drop(buffer);
        self.move_to_child(next_page_id)
    }

    fn back_to_parent(&mut self) -> bool {
        if let Some(page) = self.parent_pages.pop() {
            self.current_page = page;
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::btree::FreeblockIterator;
    use crate::header::DATABASE_HEADER_SIZE;
    use crate::pager::MAX_PAGE_SIZE;
    use crate::pager::PAGE_ID_1;
    use crate::payload::SlicePayload;
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
        assert_eq!(payload.size().get(), payload.buf().len() as u32);
        assert!(cursor.get_index_payload().is_err());
        drop(payload);
        assert_eq!(cursor.get_table_key().unwrap().unwrap(), 1);

        cursor.move_next().unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_some());
        let (key, payload) = payload.unwrap();
        assert_eq!(key, 2);
        assert_eq!(payload.buf(), &[2, 9]);
        assert_eq!(payload.size().get(), payload.buf().len() as u32);
        assert!(cursor.get_index_payload().is_err());
        drop(payload);
        assert_eq!(cursor.get_table_key().unwrap().unwrap(), 2);

        cursor.move_next().unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_some());
        let (key, payload) = payload.unwrap();
        assert_eq!(key, 3);
        assert_eq!(payload.buf(), &[2, 1, 2]);
        assert_eq!(payload.size().get(), payload.buf().len() as u32);
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
        assert_eq!(payload.size().get(), payload.buf().len() as u32);
        assert!(cursor.get_table_payload().is_err());
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_some());
        let payload = payload.unwrap();
        assert_eq!(payload.buf(), &[3, 9, 9]);
        assert_eq!(payload.size().get(), payload.buf().len() as u32);
        assert!(cursor.get_table_payload().is_err());
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_some());
        let payload = payload.unwrap();
        assert_eq!(payload.buf(), &[3, 1, 1, 2, 3]);
        assert_eq!(payload.size().get(), payload.buf().len() as u32);
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
        assert!(!cursor
            .index_move_to(&[Some(ValueCmp::new(&Value::Integer(0), &Collation::Binary))])
            .unwrap());
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
            assert!(payload.size().get() > BUFFER_SIZE as u32);
            assert_eq!(payload.size().get(), payload.buf().len() as u32);
            let mut table_record = parse_record(&payload).unwrap();
            assert_eq!(table_record.get(0).unwrap(), Some(Value::Integer(i)));
            drop(payload);
            assert_eq!(table_cursor.get_table_key().unwrap().unwrap(), i + 1);
            table_cursor.move_next().unwrap();

            let payload = index1_cursor.get_index_payload().unwrap();
            let payload = payload.unwrap();
            let mut index_record = parse_record(&payload).unwrap();
            assert_eq!(index_record.get(1).unwrap(), Some(Value::Integer(i + 1)));
            assert!(payload.size().get() > BUFFER_SIZE as u32, "{}", i);
            assert_eq!(payload.size().get(), payload.buf().len() as u32);
            drop(payload);
            index1_cursor.move_next().unwrap();

            let payload = index2_cursor.get_index_payload().unwrap();
            let payload = payload.unwrap();
            let mut index_record = parse_record(&payload).unwrap();
            assert_eq!(index_record.get(0).unwrap(), Some(Value::Integer(i)));
            assert_eq!(index_record.get(1).unwrap(), Some(Value::Integer(i + 1)));
            assert_eq!(payload.size().get(), payload.buf().len() as u32);
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
            assert_eq!(payload.size().get(), payload.buf().len() as u32);
            drop(payload);
            assert_eq!(table_cursor.get_table_key().unwrap().unwrap(), i + 1);
            table_cursor.move_next().unwrap();

            let payload = index1_cursor.get_index_payload().unwrap();
            let payload = payload.unwrap();
            let mut index_record = parse_record(&payload).unwrap();
            assert_eq!(index_record.get(1).unwrap(), Some(Value::Integer(i + 1)));
            let rowid_buf = (i as u16 + 1).to_be_bytes();
            assert_eq!(payload.buf(), &[3, 14, 2, 0xff, rowid_buf[0], rowid_buf[1]]);
            assert_eq!(payload.size().get(), payload.buf().len() as u32);
            drop(payload);
            index1_cursor.move_next().unwrap();

            let payload = index2_cursor.get_index_payload().unwrap();
            let payload = payload.unwrap();
            let mut index_record = parse_record(&payload).unwrap();
            assert_eq!(index_record.get(0).unwrap(), Some(Value::Integer(i)));
            assert_eq!(index_record.get(1).unwrap(), Some(Value::Integer(i + 1)));
            assert_eq!(payload.size().get(), payload.buf().len() as u32);
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
            Some(Value::Integer(5000))
        );
        index1_cursor
            .index_move_to(&[Some(ValueCmp::new(
                &Value::Integer(1000),
                &Collation::Binary,
            ))])
            .unwrap();
        index1_cursor.move_to_last().unwrap();
        assert_eq!(
            parse_record(&index1_cursor.get_index_payload().unwrap().unwrap())
                .unwrap()
                .get(1)
                .unwrap(),
            Some(Value::Integer(5000))
        );

        table_cursor.table_move_to(2000).unwrap();
        let payload = table_cursor.get_table_payload().unwrap();
        assert!(payload.is_some());
        let (rowid, _) = payload.unwrap();
        assert_eq!(rowid, 2000);

        assert!(!index2_cursor
            .index_move_to(&[
                Some(ValueCmp::new(&Value::Integer(2000), &Collation::Binary)),
                None
            ])
            .unwrap());
        let payload = index2_cursor.get_index_payload().unwrap();
        let payload = payload.unwrap();
        let mut index_record = parse_record(&payload).unwrap();
        assert_eq!(index_record.get(0).unwrap(), Some(Value::Integer(2000)));
        assert_eq!(index_record.get(1).unwrap(), Some(Value::Integer(2001)));
        assert_eq!(payload.size().get(), payload.buf().len() as u32);
        drop(payload);

        assert!(index2_cursor
            .index_move_to(&[
                Some(ValueCmp::new(&Value::Integer(3000), &Collation::Binary)),
                Some(ValueCmp::new(&Value::Integer(3001), &Collation::Binary)),
            ])
            .unwrap());
        let payload = index2_cursor.get_index_payload().unwrap();
        let payload = payload.unwrap();
        let mut index_record = parse_record(&payload).unwrap();
        assert_eq!(index_record.get(0).unwrap(), Some(Value::Integer(3000)));
        assert_eq!(index_record.get(1).unwrap(), Some(Value::Integer(3001)));
        assert_eq!(payload.size().get(), payload.buf().len() as u32);
        drop(payload);

        assert!(!index2_cursor
            .index_move_to(&[
                Some(ValueCmp::new(&Value::Integer(3000), &Collation::Binary)),
                Some(ValueCmp::new(&Value::Integer(3003), &Collation::Binary)),
            ])
            .unwrap());
        let payload = index2_cursor.get_index_payload().unwrap();
        let payload = payload.unwrap();
        let mut index_record = parse_record(&payload).unwrap();
        assert_eq!(index_record.get(0).unwrap(), Some(Value::Integer(3001)));
        assert_eq!(index_record.get(1).unwrap(), Some(Value::Integer(3002)));
        assert_eq!(payload.size().get(), payload.buf().len() as u32);
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
        assert_eq!(payload.size().get(), 10004);

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

        let n = payload.load(10003, &mut payload_buf).unwrap();
        assert_eq!(n, 1);

        let index_page_id = find_index_page_id("index1", file.path());

        let mut cursor = BtreeCursor::new(index_page_id, &pager, &bctx).unwrap();
        cursor.move_to_first().unwrap();

        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_some());
        let payload = payload.unwrap();

        assert_eq!(payload.buf().len(), 489);
        assert_eq!(payload.size().get(), 10004 + 1);

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

        let n = payload.load(10004, &mut payload_buf).unwrap();
        assert_eq!(n, 1);
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
            assert!(!cursor
                .index_move_to(&[Some(ValueCmp::new(
                    &Value::Integer(2 * i),
                    &Collation::Binary,
                ))])
                .unwrap());
            let payload = cursor.get_index_payload().unwrap();
            assert!(payload.is_some());
            let mut record = parse_record(payload.as_ref().unwrap()).unwrap();
            assert_eq!(record.get(0).unwrap(), Some(Value::Integer(2 * i + 1)));
            assert_eq!(record.get(1).unwrap(), Some(Value::Integer(2 * i + 1)));
            drop(payload);

            assert!(cursor
                .index_move_to(&[Some(ValueCmp::new(
                    &Value::Integer(2 * i + 1),
                    &Collation::Binary,
                ))])
                .unwrap());
            let payload = cursor.get_index_payload().unwrap();
            assert!(payload.is_some());
            let mut record = parse_record(payload.as_ref().unwrap()).unwrap();
            assert_eq!(record.get(0).unwrap(), Some(Value::Integer(2 * i + 1)));
            assert_eq!(record.get(1).unwrap(), Some(Value::Integer(2 * i + 1)));
        }

        assert!(cursor
            .index_move_to(&[Some(ValueCmp::new(&Value::Integer(10), &Collation::Binary))])
            .unwrap());
        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_some());
        let mut record = parse_record(payload.as_ref().unwrap()).unwrap();
        assert_eq!(record.get(0).unwrap(), Some(Value::Integer(10)));
        // If there are multiple entries with the same key, one of the entries is
        // returned (not necessarily the first or last one).
        assert_eq!(record.get(1).unwrap(), Some(Value::Integer(11)));
        drop(payload);

        assert!(!cursor
            .index_move_to(&[
                Some(ValueCmp::new(&Value::Integer(10), &Collation::Binary)),
                None
            ])
            .unwrap());
        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_some());
        let mut record = parse_record(payload.as_ref().unwrap()).unwrap();
        assert_eq!(record.get(0).unwrap(), Some(Value::Integer(10)));
        // Specify None to the rowid column comparator to get the first entry.
        assert_eq!(record.get(1).unwrap(), Some(Value::Integer(10)));
        drop(payload);

        for i in 10..13 {
            assert!(cursor
                .index_move_to(&[
                    Some(ValueCmp::new(&Value::Integer(10), &Collation::Binary)),
                    Some(ValueCmp::new(&Value::Integer(i), &Collation::Binary)),
                ])
                .unwrap());
            let payload = cursor.get_index_payload().unwrap();
            assert!(payload.is_some());
            let mut record = parse_record(payload.as_ref().unwrap()).unwrap();
            assert_eq!(record.get(0).unwrap(), Some(Value::Integer(10)));
            assert_eq!(record.get(1).unwrap(), Some(Value::Integer(i)));
        }

        assert!(!cursor
            .index_move_to(&[
                Some(ValueCmp::new(&Value::Integer(10), &Collation::Binary)),
                Some(ValueCmp::new(&Value::Integer(13), &Collation::Binary)),
            ])
            .unwrap());
        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_some());
        let mut record = parse_record(payload.as_ref().unwrap()).unwrap();
        assert_eq!(record.get(0).unwrap(), Some(Value::Integer(11)));
        assert_eq!(record.get(1).unwrap(), Some(Value::Integer(14)));
        drop(payload);

        assert!(!cursor
            .index_move_to(&[
                Some(ValueCmp::new(&Value::Integer(11), &Collation::Binary)),
                Some(ValueCmp::new(&Value::Integer(16), &Collation::Binary)),
            ])
            .unwrap());
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

        for (expected, comparators) in [
            (15, vec![None, None, None]),
            (
                1,
                vec![
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    None,
                    None,
                ],
            ),
            (
                2,
                vec![
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    None,
                    Some(ValueCmp::new(&Value::Integer(2), &Collation::Binary)),
                ],
            ),
            (
                4,
                vec![
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    Some(ValueCmp::new(&Value::Integer(0), &Collation::Binary)),
                    None,
                ],
            ),
            (
                3,
                vec![
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    Some(ValueCmp::new(&Value::Real(-10.1), &Collation::Binary)),
                    None,
                ],
            ),
            (
                5,
                vec![
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    Some(ValueCmp::new(&Value::Integer(5), &Collation::Binary)),
                    None,
                ],
            ),
            (
                7,
                vec![
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    Some(ValueCmp::new(&Value::Integer(101), &Collation::Binary)),
                    None,
                ],
            ),
            (
                7,
                vec![
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    Some(ValueCmp::new(
                        &Value::Text(b"".as_slice().into()),
                        &Collation::Binary,
                    )),
                    None,
                ],
            ),
            (
                8,
                vec![
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    Some(ValueCmp::new(
                        &Value::Text(b"\0".as_slice().into()),
                        &Collation::Binary,
                    )),
                    None,
                ],
            ),
            (
                10,
                vec![
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    Some(ValueCmp::new(
                        &Value::Text(b"01234".as_slice().into()),
                        &Collation::Binary,
                    )),
                    None,
                ],
            ),
            (
                10,
                vec![
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    Some(ValueCmp::new(
                        &Value::Text(b"0124".as_slice().into()),
                        &Collation::Binary,
                    )),
                    None,
                ],
            ),
            (
                13,
                vec![
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    Some(ValueCmp::new(
                        &Value::Blob([0x01, 0x24].as_slice().into()),
                        &Collation::Binary,
                    )),
                    None,
                ],
            ),
            (
                17,
                vec![
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    Some(ValueCmp::new(
                        &Value::Blob([0x01, 0x26].as_slice().into()),
                        &Collation::Binary,
                    )),
                    None,
                ],
            ),
            (
                17,
                vec![
                    Some(ValueCmp::new(&Value::Integer(2), &Collation::Binary)),
                    None,
                    None,
                ],
            ),
            (
                18,
                vec![
                    Some(ValueCmp::new(&Value::Integer(3), &Collation::Binary)),
                    None,
                    None,
                ],
            ),
            (
                21,
                vec![
                    Some(ValueCmp::new(
                        &Value::Text(b"0123".as_slice().into()),
                        &Collation::Binary,
                    )),
                    None,
                    None,
                ],
            ),
            (
                22,
                vec![
                    Some(ValueCmp::new(
                        &Value::Text(b"0123".as_slice().into()),
                        &Collation::Binary,
                    )),
                    None,
                    Some(ValueCmp::new(&Value::Integer(22), &Collation::Binary)),
                ],
            ),
            (
                24,
                vec![
                    Some(ValueCmp::new(
                        &Value::Text(b"0123".as_slice().into()),
                        &Collation::Binary,
                    )),
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    None,
                ],
            ),
            (
                27,
                vec![
                    Some(ValueCmp::new(
                        &Value::Blob([0x01, 0x24].as_slice().into()),
                        &Collation::Binary,
                    )),
                    None,
                    None,
                ],
            ),
        ] {
            cursor.index_move_to(&comparators).unwrap();
            let payload = cursor.get_index_payload().unwrap();
            assert!(payload.is_some());
            let payload = payload.unwrap();
            let mut record = parse_record(&payload).unwrap();
            if let Some(Value::Integer(rowid)) = record.get(record.len() - 1).unwrap() {
                assert_eq!(rowid, expected, "{:?}", comparators);
            } else {
                panic!("unexpected payload: {:?}", comparators);
            }
        }
    }

    #[test]
    fn test_index_move_to_collate_sequence() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col1 COLLATE BINARY, col2 COLLATE NOCASE, col3
    COLLATE RTRIM);",
            "CREATE INDEX index1 ON example(col1);",
            "CREATE INDEX index2 ON example(col2);",
            "CREATE INDEX index3 ON example(col3);",
            "INSERT INTO example(col1, col2, col3) VALUES ('abcde1', 'abcde1',
    'abcde1');",
            "INSERT INTO example(col1, col2, col3) VALUES
    ('abcde2', 'abcde2', 'abcde2');",
            "INSERT INTO example(col1,
    col2, col3) VALUES ('abcdef  ', 'abcdef  ', 'abcdef  ');",
            "INSERT INTO example(col1, col2, col3) VALUES ('ABCDEF', 'ABCDEF',
    'ABCDEF');",
            "INSERT INTO example(col1, col2, col3) VALUES
    ('ABCDE', 'ABCDE', 'ABCDE');",
            "INSERT INTO example(col1, col2,
    col3) VALUES ('ABCDE  ', 'ABCDE  ', 'ABCDE  ');",
            "INSERT INTO
    example(col1, col2, col3) VALUES ('abcde  ', 'abcde  ', 'abcde  ');",
            "INSERT INTO example(col1, col2, col3) VALUES ('abcde', 'abcde',
    'abcde');",
            "INSERT INTO example(col1, col2, col3) VALUES
    ('abcdef', 'abcdef', 'abcdef');",
            "INSERT INTO example(col1,
    col2, col3) VALUES ('ABCDEF  ', 'ABCDEF  ', 'ABCDEF  ');",
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
            let keys = vec![Some(ValueCmp::new(&key, &Collation::Binary)), None];
            cursor1.index_move_to(&keys).unwrap();
            let payload = cursor1.get_index_payload().unwrap();
            assert!(payload.is_some());
            let payload = payload.unwrap();
            let mut record = parse_record(&payload).unwrap();
            if let Some(Value::Integer(rowid)) = record.get(record.len() - 1).unwrap() {
                assert_eq!(rowid, expected[0], "{:?}", keys);
            } else {
                panic!("unexpected payload: {:?}", keys);
            }

            let keys = vec![Some(ValueCmp::new(&key, &Collation::NoCase)), None];
            cursor2.index_move_to(&keys).unwrap();
            let payload = cursor2.get_index_payload().unwrap();
            assert!(payload.is_some());
            let payload = payload.unwrap();
            let mut record = parse_record(&payload).unwrap();
            if let Some(Value::Integer(rowid)) = record.get(record.len() - 1).unwrap() {
                assert_eq!(rowid, expected[1], "{:?}", keys);
            } else {
                panic!("unexpected payload: {:?}", keys);
            }

            let keys = vec![Some(ValueCmp::new(&key, &Collation::RTrim)), None];
            cursor3.index_move_to(&keys).unwrap();
            let payload = cursor3.get_index_payload().unwrap();
            assert!(payload.is_some());
            let payload = payload.unwrap();
            let mut record = parse_record(&payload).unwrap();
            if let Some(Value::Integer(rowid)) = record.get(record.len() - 1).unwrap() {
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
            assert!(!cursor
                .index_move_to(&[Some(ValueCmp::new(&Value::Integer(i), &Collation::Binary))])
                .unwrap());
            let payload = cursor.get_index_payload().unwrap();
            assert!(payload.is_none());
        }
    }

    #[test]
    fn test_index_move_to_multiple_page() {
        // index record has 1 (header length) + 2 (bytes) + 1 (integer) bytes
        // header + at most 2 (integer) rowid.
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
                "INSERT INTO example(rowid,id, col) VALUES ({},{},
    X'FFFFFFFF');",
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
            assert!(!cursor
                .index_move_to(&[Some(ValueCmp::new(
                    &Value::Integer(2 * i),
                    &Collation::Binary,
                ))])
                .unwrap());
            let payload = cursor.get_index_payload().unwrap();
            assert!(payload.is_some(), "i = {}", i);
            let mut record = parse_record(payload.as_ref().unwrap()).unwrap();
            assert_eq!(record.get(0).unwrap(), Some(Value::Integer(2 * i + 1)));
            assert_eq!(record.get(2).unwrap(), Some(Value::Integer(i)));
            drop(payload);

            // Reset the cursor.
            cursor.move_to_first().unwrap();

            assert!(cursor
                .index_move_to(&[Some(ValueCmp::new(
                    &Value::Integer(2 * i + 1),
                    &Collation::Binary,
                ))])
                .unwrap());
            let payload = cursor.get_index_payload().unwrap();
            assert!(payload.is_some(), "i = {}", i);
            let mut record = parse_record(payload.as_ref().unwrap()).unwrap();
            assert_eq!(record.get(0).unwrap(), Some(Value::Integer(2 * i + 1)));
            assert_eq!(record.get(2).unwrap(), Some(Value::Integer(i)));
            drop(payload);

            // Reset the cursor.
            cursor.move_to_first().unwrap();
        }

        assert!(!cursor
            .index_move_to(&[Some(ValueCmp::new(
                &Value::Integer(10000),
                &Collation::Binary,
            ))])
            .unwrap());
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

        cursor
            .table_insert(1, &SlicePayload::new(&[1]).unwrap())
            .unwrap();
        cursor.move_to_first().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 1);
        assert_eq!(payload.buf(), &[1]);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_none());
        drop(payload);

        cursor
            .table_insert(2, &SlicePayload::new(&[2, 3]).unwrap())
            .unwrap();
        cursor
            .table_insert(4, &SlicePayload::new(&[4, 5, 6, 7]).unwrap())
            .unwrap();

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

        cursor
            .table_insert(-1, &SlicePayload::new(&[255]).unwrap())
            .unwrap();
        cursor
            .table_insert(3, &SlicePayload::new(&[]).unwrap())
            .unwrap();

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

        cursor
            .table_insert(6, &SlicePayload::new(&[6]).unwrap())
            .unwrap();
        cursor
            .table_insert(-1, &SlicePayload::new(&[255]).unwrap())
            .unwrap();
        cursor
            .table_insert(3, &SlicePayload::new(&[3]).unwrap())
            .unwrap();

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
            Some(Value::Integer(1))
        );
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 2);
        assert_eq!(
            parse_record(&payload).unwrap().get(0).unwrap(),
            Some(Value::Integer(2))
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
            Some(Value::Integer(5))
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
    fn test_insert_table_max_page_size() {
        let file =
            create_sqlite_database(&["PRAGMA page_size = 65536;", "CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());

        let page_1 = pager.get_page(PAGE_ID_1).unwrap();
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
        cursor
            .table_insert(1, &SlicePayload::new(&[1]).unwrap())
            .unwrap();
        cursor.move_to_first().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 1);
        assert_eq!(payload.buf(), &[1]);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_none());
        drop(payload);

        assert_eq!(bctx.max_local(true), 65501);
        cursor
            .table_insert(2, &SlicePayload::new(&[2; 65490]).unwrap())
            .unwrap();
        cursor
            .table_insert(4, &SlicePayload::new(&[4; 65490]).unwrap())
            .unwrap();
        cursor
            .table_insert(3, &SlicePayload::new(&[3; 65490]).unwrap())
            .unwrap();

        cursor.table_move_to(2).unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 2);
        assert_eq!(payload.buf(), &[2; 65490]);
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 3);
        assert_eq!(payload.buf(), &[3; 65490]);
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 4);
        assert_eq!(payload.buf(), &[4; 65490]);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_none());
    }

    #[test]
    fn test_insert_table_overflow() {
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
            cursor
                .table_insert(1, &SlicePayload::new(&data[..max_local]).unwrap())
                .unwrap();
            cursor.table_move_to(1).unwrap();
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, 1);
            assert_eq!(payload.size().get() as usize, max_local);
            assert_eq!(payload.buf().len(), max_local);
            assert_eq!(payload.buf(), &data[..max_local]);
        }
        pager.abort();

        // Overflows
        let payload_size = max_local + 1;
        {
            let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();
            cursor
                .table_insert(2, &SlicePayload::new(&data[..payload_size]).unwrap())
                .unwrap();
            cursor.table_move_to(2).unwrap();
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, 2);
            assert_eq!(payload.size().get() as usize, payload_size);
            assert!(payload.buf().len() < payload_size);
            let mut buf = vec![0; payload_size + 1];
            let loaded = payload.load(0, &mut buf).unwrap();
            assert_eq!(loaded, payload_size);
            assert_eq!(&buf[..payload_size], &data[..payload_size]);
        }
        pager.abort();

        // Overflows with exact overflow page size
        let mut size_exact_overflow_page_size = None;
        for i in 1..4096 {
            let p_size = max_local + i;
            let p_size = (p_size as u64).try_into().unwrap();
            let n_local = bctx.n_local(true, p_size) as usize;
            if (p_size.get() as usize - n_local) % (bctx.usable_size as usize - 4) == 0 {
                size_exact_overflow_page_size = Some(p_size);
                break;
            }
        }
        assert!(size_exact_overflow_page_size.is_some());
        assert_eq!(size_exact_overflow_page_size.unwrap().get(), 4581);
        let payload_size = size_exact_overflow_page_size.unwrap().get() as usize;
        {
            let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();
            cursor
                .table_insert(3, &SlicePayload::new(&data[..payload_size]).unwrap())
                .unwrap();
            cursor.table_move_to(3).unwrap();
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, 3);
            assert_eq!(payload.size().get() as usize, payload_size);
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
            cursor
                .table_insert(4, &SlicePayload::new(&data[..payload_size]).unwrap())
                .unwrap();
            cursor.table_move_to(4).unwrap();
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, 4);
            assert_eq!(payload.size().get() as usize, payload_size);
            assert!(payload.buf().len() < payload_size);
            let mut buf = vec![0; payload_size + 1];
            let loaded = payload.load(0, &mut buf).unwrap();
            assert_eq!(loaded, payload_size);
            assert_eq!(&buf[..payload_size], &data[..payload_size]);
        }
        pager.abort();
    }

    fn assert_all_local_in_table_cursor(cursor: &mut BtreeCursor, values: &[(i64, &[u8])]) {
        for (expected_key, expected_buf) in values {
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, *expected_key);
            assert_eq!(payload.buf(), *expected_buf);
            drop(payload);
            cursor.move_next().unwrap();
        }
        assert!(cursor.get_table_payload().unwrap().is_none());
    }

    #[test]
    fn test_insert_table_from_freeblock_split() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "INSERT INTO example(rowid, col) VALUES (1, x'01');",
            "INSERT INTO example(rowid, col) VALUES (2, x'0202');",
            "INSERT INTO example(rowid, col) VALUES (3, x'ffffffffffffffff');", // 8 bytes
            "INSERT INTO example(rowid, col) VALUES (4, x'04');",
            "DELETE FROM example WHERE rowid = 1;",
            "DELETE FROM example WHERE rowid = 3;",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());

        let page = pager.get_page(table_page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        assert_eq!(page_header.first_freeblock_offset(), 4073);
        assert_eq!(page_header.fragmented_free_bytes(), 0);
        assert_eq!(page_header.cell_content_area_offset().get(), 4068);
        drop(buffer);

        let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();

        cursor
            .table_insert(5, &SlicePayload::new(&[2, 20, 5, 5, 5, 5]).unwrap())
            .unwrap();

        cursor.move_to_first().unwrap();
        assert_all_local_in_table_cursor(
            &mut cursor,
            &[
                (2, &[2, 16, 2, 2]),
                (4, &[2, 14, 4]),
                (5, &[2, 20, 5, 5, 5, 5]),
            ],
        );

        let page = pager.get_page(table_page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        assert_eq!(page_header.first_freeblock_offset(), 4081);
        assert_eq!(page_header.fragmented_free_bytes(), 0);
        assert_eq!(page_header.cell_content_area_offset().get(), 4068);

        let mut freeblocks = FreeblockIterator::new(page_header.first_freeblock_offset(), &buffer);

        assert_eq!(freeblocks.next(), Some((4081, 4)));
        assert_eq!(freeblocks.next(), Some((4091, 5)));
        assert_eq!(freeblocks.next(), None);
    }

    #[test]
    fn test_insert_table_from_freeblock_skipping_small_freeblock() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "INSERT INTO example(rowid, col) VALUES (1, x'ffffffffffffffff');", // 8 bytes
            "INSERT INTO example(rowid, col) VALUES (2, x'0202');",
            "INSERT INTO example(rowid, col) VALUES (3, x'03');",
            "INSERT INTO example(rowid, col) VALUES (4, x'04');",
            "DELETE FROM example WHERE rowid = 1;",
            "DELETE FROM example WHERE rowid = 3;",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());

        let page = pager.get_page(table_page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        assert_eq!(page_header.first_freeblock_offset(), 4073);
        assert_eq!(page_header.fragmented_free_bytes(), 0);
        assert_eq!(page_header.cell_content_area_offset().get(), 4068);
        drop(buffer);

        let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();

        cursor
            .table_insert(5, &SlicePayload::new(&[2, 20, 5, 5, 5, 5]).unwrap())
            .unwrap();

        cursor.move_to_first().unwrap();
        assert_all_local_in_table_cursor(
            &mut cursor,
            &[
                (2, &[2, 16, 2, 2]),
                (4, &[2, 14, 4]),
                (5, &[2, 20, 5, 5, 5, 5]),
            ],
        );

        let page = pager.get_page(table_page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        assert_eq!(page_header.first_freeblock_offset(), 4073);
        assert_eq!(page_header.fragmented_free_bytes(), 0);
        assert_eq!(page_header.cell_content_area_offset().get(), 4068);

        let mut freeblocks = FreeblockIterator::new(page_header.first_freeblock_offset(), &buffer);

        assert_eq!(freeblocks.next(), Some((4073, 5)));
        assert_eq!(freeblocks.next(), Some((4092, 4)));
        assert_eq!(freeblocks.next(), None);
    }

    #[test]
    fn test_insert_table_from_freeblock_fragmented() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "INSERT INTO example(rowid, col) VALUES (1, x'01');",
            "INSERT INTO example(rowid, col) VALUES (2, x'0202');",
            "INSERT INTO example(rowid, col) VALUES (3, x'ffffffffffffffff');", // 8 bytes
            "INSERT INTO example(rowid, col) VALUES (4, x'04');",
            "DELETE FROM example WHERE rowid = 1;",
            "DELETE FROM example WHERE rowid = 3;",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());

        let page = pager.get_page(table_page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        assert_eq!(page_header.first_freeblock_offset(), 4073);
        assert_eq!(page_header.fragmented_free_bytes(), 0);
        assert_eq!(page_header.cell_content_area_offset().get(), 4068);
        drop(buffer);

        let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();

        cursor
            .table_insert(5, &SlicePayload::new(&[2, 22, 5, 5, 5, 5, 5]).unwrap())
            .unwrap();

        cursor.move_to_first().unwrap();
        assert_all_local_in_table_cursor(
            &mut cursor,
            &[
                (2, &[2, 16, 2, 2]),
                (4, &[2, 14, 4]),
                (5, &[2, 22, 5, 5, 5, 5, 5]),
            ],
        );

        let page = pager.get_page(table_page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        assert_eq!(page_header.first_freeblock_offset(), 4091);
        assert_eq!(page_header.fragmented_free_bytes(), 3);
        assert_eq!(page_header.cell_content_area_offset().get(), 4068);

        let mut freeblocks = FreeblockIterator::new(page_header.first_freeblock_offset(), &buffer);

        assert_eq!(freeblocks.next(), Some((4091, 5)));
        assert_eq!(freeblocks.next(), None);
    }

    #[test]
    fn test_insert_table_from_freeblock_fragment_threshold() {
        let mut stmts = vec!["CREATE TABLE example(col);"];
        // Create total 57 bytes fragments.
        for _ in 0..57 {
            // all rowid is bigger than 200 which takes 2 bytes as varint.
            stmts.push("INSERT INTO example(rowid, col) VALUES (200, x'0102030405060708');");
            stmts.push("INSERT INTO example(col) VALUES (NULL);");
            stmts.push("DELETE FROM example WHERE rowid = 200;");
            // Adds 1 byte of fragment.
            stmts.push("INSERT INTO example(col) VALUES (x'01020304050607');");
        }
        // Create 2 freeblocks.
        stmts.push("INSERT INTO example(rowid, col) VALUES (200, x'0102030405060708');");
        stmts.push("INSERT INTO example(col) VALUES (NULL);");
        stmts.push("DELETE FROM example WHERE rowid = 200;");
        stmts.push("INSERT INTO example(rowid, col) VALUES (200, x'010203040506070809');");
        stmts.push("INSERT INTO example(col) VALUES (x'01020304050607080a');");
        stmts.push("DELETE FROM example WHERE rowid = 200;");
        let file = create_sqlite_database(&stmts);

        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());

        let page = pager.get_page(table_page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        assert_eq!(page_header.first_freeblock_offset(), 3038);
        assert_eq!(page_header.fragmented_free_bytes(), 57);
        assert_eq!(page_header.cell_content_area_offset().get(), 3024);
        drop(buffer);

        let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();

        cursor
            .table_insert(
                400,
                &SlicePayload::new(&[2, 28, 1, 2, 3, 4, 5, 6, 7, 8]).unwrap(),
            )
            .unwrap();

        let page = pager.get_page(table_page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        for (offset, size) in FreeblockIterator::new(page_header.first_freeblock_offset(), &buffer)
        {
            println!("offset = {}, size = {}", offset, size);
        }
        assert_eq!(page_header.first_freeblock_offset(), 3057);
        assert_eq!(page_header.fragmented_free_bytes(), 58);
        assert_eq!(page_header.cell_content_area_offset().get(), 3024);
        drop(buffer);

        cursor
            .table_insert(401, &SlicePayload::new(&[2, 0]).unwrap())
            .unwrap();

        // Use unallocated space while there is a freeblock because fragment size is
        // bigger than 57.
        let page = pager.get_page(table_page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        assert_eq!(page_header.first_freeblock_offset(), 3057);
        assert_eq!(page_header.fragmented_free_bytes(), 58);
        assert_eq!(page_header.cell_content_area_offset().get(), 3019);
    }

    #[test]
    fn test_insert_table_skipping_all_freeblock() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "INSERT INTO example(rowid, col) VALUES (1, x'01');",
            "INSERT INTO example(rowid, col) VALUES (2, x'0202');",
            "INSERT INTO example(rowid, col) VALUES (3, x'ffffffffffffffff');", // 8 bytes
            "INSERT INTO example(rowid, col) VALUES (4, x'04');",
            "DELETE FROM example WHERE rowid = 1;",
            "DELETE FROM example WHERE rowid = 3;",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());

        let page = pager.get_page(table_page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        assert_eq!(page_header.first_freeblock_offset(), 4073);
        assert_eq!(page_header.fragmented_free_bytes(), 0);
        assert_eq!(page_header.cell_content_area_offset().get(), 4068);
        drop(buffer);

        let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();

        cursor
            .table_insert(
                5,
                &SlicePayload::new(&[2, 32, 9, 9, 9, 9, 9, 9, 9, 9, 9]).unwrap(),
            )
            .unwrap();

        cursor.move_to_first().unwrap();
        assert_all_local_in_table_cursor(
            &mut cursor,
            &[
                (2, &[2, 16, 2, 2]),
                (4, &[2, 14, 4]),
                (5, &[2, 32, 9, 9, 9, 9, 9, 9, 9, 9, 9]),
            ],
        );

        let page = pager.get_page(table_page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        assert_eq!(page_header.first_freeblock_offset(), 4073);
        assert_eq!(page_header.fragmented_free_bytes(), 0);
        assert_eq!(page_header.cell_content_area_offset().get(), 4055);

        let mut freeblocks = FreeblockIterator::new(page_header.first_freeblock_offset(), &buffer);

        assert_eq!(freeblocks.next(), Some((4073, 12)));
        assert_eq!(freeblocks.next(), Some((4091, 5)));
        assert_eq!(freeblocks.next(), None);
    }

    #[test]
    fn test_insert_table_defragment() {
        let insert_1001byte_stmt_1 = format!(
            "INSERT INTO example(rowid, col) VALUES (1, x'{}');",
            "11".repeat(1001)
        );
        let insert_1001byte_stmt_2 = format!(
            "INSERT INTO example(rowid, col) VALUES (2, x'{}');",
            "22".repeat(1001)
        );
        let insert_1000byte_stmt_3 = format!(
            "INSERT INTO example(rowid, col) VALUES (3, x'{}');",
            "33".repeat(1000)
        );
        let insert_1001byte_stmt_4 = format!(
            "INSERT INTO example(rowid, col) VALUES (4, x'{}');",
            "44".repeat(1001)
        );
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            &insert_1001byte_stmt_1,
            &insert_1001byte_stmt_2,
            "DELETE FROM example WHERE rowid = 1;",
            &insert_1000byte_stmt_3,
            &insert_1001byte_stmt_1,
            &insert_1001byte_stmt_4,
            "DELETE FROM example WHERE rowid = 1;",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());

        let page = pager.get_page(table_page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        assert_eq!(page_header.first_freeblock_offset(), 1075);
        assert_eq!(page_header.fragmented_free_bytes(), 1);
        assert_eq!(page_header.cell_content_area_offset().get(), 68);
        assert_eq!(
            FreeblockIterator::new(page_header.first_freeblock_offset(), &buffer)
                .next()
                .unwrap(),
            (1075, 1007)
        );
        drop(buffer);

        let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();

        let payload5 = [5; 1008];
        cursor
            .table_insert(5, &SlicePayload::new(&payload5).unwrap())
            .unwrap();

        let page = pager.get_page(table_page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        assert_eq!(page_header.first_freeblock_offset(), 0);
        assert_eq!(page_header.fragmented_free_bytes(), 0);
        assert_eq!(page_header.cell_content_area_offset().get(), 65);
        drop(buffer);

        cursor.move_to_first().unwrap();

        let mut payload2 = vec![3, 143, 94];
        payload2.extend(&[0x22; 1001]);
        let mut payload3 = vec![3, 143, 92];
        payload3.extend(&[0x33; 1000]);
        let mut payload4 = vec![3, 143, 94];
        payload4.extend(&[0x44; 1001]);
        assert_all_local_in_table_cursor(
            &mut cursor,
            &[
                (2, &payload2),
                (3, &payload3),
                (4, &payload4),
                (5, &payload5),
            ],
        );
    }

    #[test]
    fn test_insert_table_defragment_page1() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();

        let page = pager.get_page(PAGE_ID_1).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        let page_type = page_header.page_type();
        let cell_content_area_offset = page_header.cell_content_area_offset().get() as usize;
        let header_vec = buffer[..DATABASE_HEADER_SIZE].to_vec();
        drop(buffer);

        let mut buffer = pager.make_page_mut(&page).unwrap();
        let freeblock_offset = cell_content_area_offset - 10;
        set_u16(&mut buffer, freeblock_offset, 0);
        set_u16(&mut buffer, freeblock_offset + 2, 10);
        let mut page_header = BtreePageHeaderMut::from_page(&page, &mut buffer);
        page_header.set_first_freeblock_offset(freeblock_offset as u16);
        page_header.add_fragmented_free_bytes(3);
        page_header.set_cell_content_area_offset(
            cell_pointer_offset(&page, 1, page_type.header_size()) as u16 + 10,
        );
        drop(buffer);

        let mut cursor = BtreeCursor::new(PAGE_ID_1, &pager, &bctx).unwrap();

        let payload = [5; 10];
        cursor
            .table_insert(30, &SlicePayload::new(&payload).unwrap())
            .unwrap();

        let page = pager.get_page(PAGE_ID_1).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        assert_eq!(page_header.first_freeblock_offset(), 0);
        assert_eq!(page_header.fragmented_free_bytes(), 0);
        assert_eq!(page_header.cell_content_area_offset().get(), 4031);
        // database header is preserved.
        assert_eq!(&buffer[..DATABASE_HEADER_SIZE], &header_vec);

        drop(buffer);

        cursor.move_to_first().unwrap();
        assert_all_local_in_table_cursor(
            &mut cursor,
            &[
                (
                    1,
                    &[
                        6, 23, 27, 27, 1, 63, 116, 97, 98, 108, 101, 101, 120, 97, 109, 112, 108,
                        101, 101, 120, 97, 109, 112, 108, 101, 2, 67, 82, 69, 65, 84, 69, 32, 84,
                        65, 66, 76, 69, 32, 101, 120, 97, 109, 112, 108, 101, 40, 99, 111, 108, 41,
                    ],
                ),
                (30, &payload),
            ],
        );
    }

    #[test]
    fn test_insert_table_split() {
        let file =
            create_sqlite_database(&["PRAGMA page_size = 512;", "CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();
        for i in 0..1000 {
            cursor
                .table_insert(i, &SlicePayload::new(&[(i % 256) as u8; 200]).unwrap())
                .unwrap();
        }
        // Overflow payloads
        for i in 1000..2000 {
            cursor
                .table_insert(i, &SlicePayload::new(&[(i % 256) as u8; 1000]).unwrap())
                .unwrap();
        }

        cursor.move_to_first().unwrap();
        for i in 0..1000 {
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, i);
            assert_eq!(payload.buf(), &[(i % 256) as u8; 200]);
            drop(payload);
            cursor.move_next().unwrap();
        }
        for i in 1000..2000 {
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, i);
            assert_eq!(payload.size().get(), 1000);
            let mut buf = [0; 1001];
            assert_eq!(payload.load(0, &mut buf).unwrap(), 1000);
            assert_eq!(&buf[..1000], &[(i % 256) as u8; 1000]);
            drop(payload);
            cursor.move_next().unwrap();
        }
        assert!(cursor.get_table_payload().unwrap().is_none());
    }

    #[test]
    fn test_insert_table_split_reversed() {
        let file =
            create_sqlite_database(&["PRAGMA page_size = 512;", "CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();
        for i in 0..1000 {
            cursor
                .table_insert(
                    i64::MAX - i,
                    &SlicePayload::new(&[(i % 256) as u8; 200]).unwrap(),
                )
                .unwrap();
        }

        cursor.move_to_first().unwrap();
        for i in 0..1000 {
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, i64::MAX - 999 + i);
            assert_eq!(payload.buf(), &[((999 - i) % 256) as u8; 200]);
            drop(payload);
            cursor.move_next().unwrap();
        }
        assert!(cursor.get_table_payload().unwrap().is_none());
    }

    #[test]
    fn test_insert_table_split_holes() {
        let file =
            create_sqlite_database(&["PRAGMA page_size = 512;", "CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();
        for i in 0..4 {
            for j in 0..1000 {
                cursor
                    .table_insert(
                        4 * j + i,
                        &SlicePayload::new(&[((4 * j + i) % 256) as u8; 200]).unwrap(),
                    )
                    .unwrap();
            }
        }

        cursor.move_to_first().unwrap();
        for i in 0..4000 {
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, i);
            assert_eq!(payload.buf(), &[(i % 256) as u8; 200]);
            drop(payload);
            cursor.move_next().unwrap();
        }
        assert!(cursor.get_table_payload().unwrap().is_none());
    }

    #[test]
    fn test_insert_table_split_page1() {
        let file =
            create_sqlite_database(&["PRAGMA page_size = 512;", "CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();

        let mut cursor = BtreeCursor::new(PAGE_ID_1, &pager, &bctx).unwrap();
        cursor.move_to_first().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 1);
        assert_eq!(payload.buf().len(), payload.size().get() as usize);
        let payload1 = payload.buf().to_vec();
        drop(payload);

        for i in 1..1000 {
            cursor
                .table_insert(key + i, &SlicePayload::new(&[(i % 256) as u8; 50]).unwrap())
                .unwrap();
        }

        cursor.move_to_first().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 1);
        assert_eq!(payload.buf(), &payload1);
        drop(payload);

        for i in 1..1000 {
            cursor.move_next().unwrap();
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, i + 1);
            assert_eq!(payload.buf(), &[(i % 256) as u8; 50]);
        }
        cursor.move_next().unwrap();
        assert!(cursor.get_table_payload().unwrap().is_none());
    }

    #[test]
    fn test_insert_table_split_1_cell_per_page() {
        let file =
            create_sqlite_database(&["PRAGMA page_size = 512;", "CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();
        // On inserting key = 128 and splitting a page, the content size of right page
        // is bigger than left page.
        for i in 0..1000 {
            cursor
                .table_insert(i, &SlicePayload::new(&[(i % 256) as u8; 450]).unwrap())
                .unwrap();
        }

        cursor.move_to_first().unwrap();
        for i in 0..1000 {
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, i);
            assert_eq!(payload.buf(), &[(i % 256) as u8; 450]);
            drop(payload);
            cursor.move_next().unwrap();
        }
        assert!(cursor.get_table_payload().unwrap().is_none());
    }

    #[test]
    fn test_insert_table_split_into_3pages() {
        let file =
            create_sqlite_database(&["PRAGMA page_size = 512;", "CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();
        cursor
            .table_insert(1, &SlicePayload::new(&[1; 200]).unwrap())
            .unwrap();
        cursor
            .table_insert(3, &SlicePayload::new(&[3; 200]).unwrap())
            .unwrap();
        cursor
            .table_insert(2, &SlicePayload::new(&[2; 400]).unwrap())
            .unwrap();

        cursor.move_to_first().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 1);
        assert_eq!(payload.buf(), &[1; 200]);
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 2);
        assert_eq!(payload.buf(), &[2; 400]);
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 3);
        assert_eq!(payload.buf(), &[3; 200]);
        drop(payload);

        cursor.move_next().unwrap();
        assert!(cursor.get_table_payload().unwrap().is_none());
    }

    #[test]
    fn test_insert_table_split_into_3pages_split_interior_again() {
        let file =
            create_sqlite_database(&["PRAGMA page_size = 512;", "CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();
        for i in 0..141 {
            cursor
                .table_insert(i, &SlicePayload::new(&[i as u8; 200]).unwrap())
                .unwrap();
        }
        cursor
            .table_insert(142, &SlicePayload::new(&[142; 200]).unwrap())
            .unwrap();
        let root_page = pager.get_page(page_id).unwrap();
        let buffer = root_page.buffer();
        let page_header = BtreePageHeader::from_page(&root_page, &buffer);
        assert!(!page_header.page_type().is_leaf());
        assert_eq!(page_header.n_cells(), 70);
        drop(buffer);
        // The interiror page has no room for 1 cell.
        cursor
            .table_insert(141, &SlicePayload::new(&[141; 400]).unwrap())
            .unwrap();
        let buffer = root_page.buffer();
        let page_header = BtreePageHeader::from_page(&root_page, &buffer);
        assert!(!page_header.page_type().is_leaf());
        assert_eq!(page_header.n_cells(), 1);
        drop(buffer);

        cursor.move_to_first().unwrap();

        for i in 0..141 {
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, i);
            assert_eq!(payload.buf(), &[i as u8; 200]);
            drop(payload);
            cursor.move_next().unwrap();
        }

        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 141);
        assert_eq!(payload.buf(), &[141; 400]);
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 142);
        assert_eq!(payload.buf(), &[142; 200]);
        drop(payload);

        cursor.move_next().unwrap();
        assert!(cursor.get_table_payload().unwrap().is_none());
    }

    #[test]
    fn test_insert_table_split_into_3pages_split_interior_again2() {
        let file =
            create_sqlite_database(&["PRAGMA page_size = 512;", "CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();
        for i in 0..139 {
            cursor
                .table_insert(i, &SlicePayload::new(&[i as u8; 200]).unwrap())
                .unwrap();
        }
        cursor
            .table_insert(140, &SlicePayload::new(&[140; 200]).unwrap())
            .unwrap();
        let root_page = pager.get_page(page_id).unwrap();
        let buffer = root_page.buffer();
        let page_header = BtreePageHeader::from_page(&root_page, &buffer);
        assert!(!page_header.page_type().is_leaf());
        assert_eq!(page_header.n_cells(), 69);
        drop(buffer);
        // The interiror page has room for 1 cell.
        cursor
            .table_insert(139, &SlicePayload::new(&[139; 400]).unwrap())
            .unwrap();
        let buffer = root_page.buffer();
        let page_header = BtreePageHeader::from_page(&root_page, &buffer);
        assert!(!page_header.page_type().is_leaf());
        assert_eq!(page_header.n_cells(), 1);
        drop(buffer);

        cursor.move_to_first().unwrap();

        for i in 0..139 {
            let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
            assert_eq!(key, i);
            assert_eq!(payload.buf(), &[i as u8; 200]);
            drop(payload);
            cursor.move_next().unwrap();
        }

        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 139);
        assert_eq!(payload.buf(), &[139; 400]);
        drop(payload);

        cursor.move_next().unwrap();
        let (key, payload) = cursor.get_table_payload().unwrap().unwrap();
        assert_eq!(key, 140);
        assert_eq!(payload.buf(), &[140; 200]);
        drop(payload);

        cursor.move_next().unwrap();
        assert!(cursor.get_table_payload().unwrap().is_none());
    }

    #[test]
    fn test_insert_empty_index() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE INDEX index1 ON example(col);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let index_page_id = find_index_page_id("index1", file.path());

        let mut cursor = BtreeCursor::new(index_page_id, &pager, &bctx).unwrap();

        let payload1 = build_record(&[Some(&Value::Integer(1)), Some(&Value::Integer(1))]);
        cursor
            .index_insert(
                &[
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                ],
                &SlicePayload::new(&payload1).unwrap(),
            )
            .unwrap();
        cursor.move_to_first().unwrap();
        let payload = cursor.get_index_payload().unwrap().unwrap();
        assert_eq!(payload.buf(), &payload1);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_none());
        drop(payload);

        let payload2 = build_record(&[Some(&Value::Integer(1)), Some(&Value::Integer(4))]);
        let payload3 = build_record(&[Some(&Value::Integer(4)), Some(&Value::Integer(3))]);
        cursor
            .index_insert(
                &[
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    Some(ValueCmp::new(&Value::Integer(2), &Collation::Binary)),
                ],
                &SlicePayload::new(&payload2).unwrap(),
            )
            .unwrap();
        cursor
            .index_insert(
                &[
                    Some(ValueCmp::new(&Value::Integer(4), &Collation::Binary)),
                    Some(ValueCmp::new(&Value::Integer(3), &Collation::Binary)),
                ],
                &SlicePayload::new(&payload3).unwrap(),
            )
            .unwrap();

        cursor.move_to_first().unwrap();
        let payload = cursor.get_index_payload().unwrap().unwrap();
        assert_eq!(payload.buf(), &payload1);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_index_payload().unwrap().unwrap();
        assert_eq!(payload.buf(), &payload2);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_index_payload().unwrap().unwrap();
        assert_eq!(payload.buf(), &payload3);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_none());
        drop(payload);

        let payload4 = build_record(&[Some(&Value::Integer(1)), Some(&Value::Integer(-1))]);
        let payload5 = build_record(&[Some(&Value::Integer(1)), Some(&Value::Integer(2))]);
        let payload6 = build_record(&[Some(&Value::Integer(2)), Some(&Value::Integer(5))]);
        cursor
            .index_insert(
                &[
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    Some(ValueCmp::new(&Value::Integer(-1), &Collation::Binary)),
                ],
                &SlicePayload::new(&payload4).unwrap(),
            )
            .unwrap();
        cursor
            .index_insert(
                &[
                    Some(ValueCmp::new(&Value::Integer(1), &Collation::Binary)),
                    Some(ValueCmp::new(&Value::Integer(2), &Collation::Binary)),
                ],
                &SlicePayload::new(&payload5).unwrap(),
            )
            .unwrap();
        cursor
            .index_insert(
                &[
                    Some(ValueCmp::new(&Value::Integer(2), &Collation::Binary)),
                    Some(ValueCmp::new(&Value::Integer(5), &Collation::Binary)),
                ],
                &SlicePayload::new(&payload6).unwrap(),
            )
            .unwrap();

        cursor.move_to_first().unwrap();
        let payload = cursor.get_index_payload().unwrap().unwrap();
        assert_eq!(payload.buf(), &payload4);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_index_payload().unwrap().unwrap();
        assert_eq!(payload.buf(), &payload1);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_index_payload().unwrap().unwrap();
        assert_eq!(payload.buf(), &payload5);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_index_payload().unwrap().unwrap();
        assert_eq!(payload.buf(), &payload2);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_index_payload().unwrap().unwrap();
        assert_eq!(payload.buf(), &payload6);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_index_payload().unwrap().unwrap();
        assert_eq!(payload.buf(), &payload3);
        drop(payload);

        cursor.move_next().unwrap();
        let payload = cursor.get_index_payload().unwrap();
        assert!(payload.is_none());
        drop(payload);
    }

    #[test]
    fn test_insert_index_overflow() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE INDEX index1 ON example(col);",
        ]);

        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let index_page_id = find_index_page_id("index1", file.path());
        let max_local = bctx.max_local(false) as usize;
        let usable_size = bctx.usable_size as usize;

        let mut data = Vec::with_capacity(usable_size * 2);
        for _ in 0..usable_size * 2 {
            data.push(rand::random::<u8>());
        }

        // Not overflow
        {
            let mut cursor = BtreeCursor::new(index_page_id, &pager, &bctx).unwrap();
            let value = Value::Blob(data[..max_local - 3].into());
            let record_payload = build_record(&[Some(&value)]);
            assert_eq!(record_payload.len(), max_local);
            let comparator = [Some(ValueCmp::new(&value, &Collation::Binary))];
            cursor
                .index_insert(&comparator, &SlicePayload::new(&record_payload).unwrap())
                .unwrap();
            cursor.index_move_to(&comparator).unwrap();
            let payload = cursor.get_index_payload().unwrap().unwrap();
            assert_eq!(payload.size().get() as usize, max_local);
            assert_eq!(payload.buf().len(), max_local);
            assert_eq!(payload.buf(), &record_payload);
        }
        pager.abort();

        // Overflows
        let payload_size = max_local + 1;
        {
            let mut cursor = BtreeCursor::new(index_page_id, &pager, &bctx).unwrap();
            let value = Value::Blob(data[..payload_size - 3].into());
            let record_payload = build_record(&[Some(&value)]);
            assert_eq!(record_payload.len(), payload_size);
            let comparator = [Some(ValueCmp::new(&value, &Collation::Binary))];
            cursor
                .index_insert(&comparator, &SlicePayload::new(&record_payload).unwrap())
                .unwrap();
            cursor.index_move_to(&comparator).unwrap();
            let payload = cursor.get_index_payload().unwrap().unwrap();
            assert_eq!(payload.size().get() as usize, payload_size);
            assert!(payload.buf().len() < payload_size);
            let mut buf = vec![0; payload_size + 1];
            let loaded = payload.load(0, &mut buf).unwrap();
            assert_eq!(loaded, payload_size);
            assert_eq!(&buf[..payload_size], &record_payload);
        }
        pager.abort();

        // Overflows with exact overflow page size
        let mut size_exact_overflow_page_size = None;
        for i in 1..4096 {
            let p_size = max_local + i;
            let p_size = (p_size as u64).try_into().unwrap();
            let n_local = bctx.n_local(false, p_size) as usize;
            if (p_size.get() as usize - n_local) % (bctx.usable_size as usize - 4) == 0 {
                size_exact_overflow_page_size = Some(p_size);
                break;
            }
        }
        assert!(size_exact_overflow_page_size.is_some());
        assert_eq!(size_exact_overflow_page_size.unwrap().get(), 4581);
        let payload_size = size_exact_overflow_page_size.unwrap().get() as usize;
        {
            let mut cursor = BtreeCursor::new(index_page_id, &pager, &bctx).unwrap();
            let value = Value::Blob(data[..payload_size - 3].into());
            let record_payload = build_record(&[Some(&value)]);
            assert_eq!(record_payload.len(), payload_size);
            let comparator = [Some(ValueCmp::new(&value, &Collation::Binary))];
            cursor
                .index_insert(&comparator, &SlicePayload::new(&record_payload).unwrap())
                .unwrap();
            cursor.index_move_to(&comparator).unwrap();
            let payload = cursor.get_index_payload().unwrap().unwrap();
            assert_eq!(payload.size().get() as usize, payload_size);
            assert!(payload.buf().len() < payload_size);
            let mut buf = vec![0; payload_size + 1];
            let loaded = payload.load(0, &mut buf).unwrap();
            assert_eq!(loaded, payload_size);
            assert_eq!(&buf[..payload_size], &record_payload);
        }
        pager.abort();

        // Overflow with multiple overflow pages.
        let payload_size = usable_size * 2;
        {
            let mut cursor = BtreeCursor::new(index_page_id, &pager, &bctx).unwrap();
            let value = Value::Blob(data[..payload_size - 4].into());
            let record_payload = build_record(&[Some(&value)]);
            assert_eq!(record_payload.len(), payload_size);
            let comparator = [Some(ValueCmp::new(&value, &Collation::Binary))];
            cursor
                .index_insert(&comparator, &SlicePayload::new(&record_payload).unwrap())
                .unwrap();
            cursor.index_move_to(&comparator).unwrap();
            let payload = cursor.get_index_payload().unwrap().unwrap();
            assert_eq!(payload.size().get() as usize, payload_size);
            assert!(payload.buf().len() < payload_size);
            let mut buf = vec![0; payload_size + 1];
            let loaded = payload.load(0, &mut buf).unwrap();
            assert_eq!(loaded, payload_size);
            assert_eq!(&buf[..payload_size], &record_payload);
        }
        pager.abort();
    }

    fn assert_all_local_in_index_cursor(cursor: &mut BtreeCursor, values: &[&[u8]]) {
        for expected in values {
            let payload = cursor.get_index_payload().unwrap().unwrap();
            assert_eq!(payload.buf(), *expected);
            drop(payload);
            cursor.move_next().unwrap();
        }
        assert!(cursor.get_index_payload().unwrap().is_none());
    }

    #[test]
    fn test_insert_index_defragment() {
        let insert_901byte_stmt_2 = format!(
            "INSERT INTO example(rowid, col) VALUES (2, x'{}');",
            "22".repeat(901)
        );
        let insert_901byte_stmt_3 = format!(
            "INSERT INTO example(rowid, col) VALUES (3, x'{}');",
            "33".repeat(901)
        );
        let insert_900byte_stmt_4 = format!(
            "INSERT INTO example(rowid, col) VALUES (4, x'{}');",
            "44".repeat(900)
        );
        // The payload will overflow.
        let insert_2000byte_stmt_5 = format!(
            "INSERT INTO example(rowid, col) VALUES (5, x'{}');",
            "55".repeat(2000)
        );
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE INDEX index1 ON example(col);",
            &insert_901byte_stmt_2,
            &insert_901byte_stmt_3,
            "DELETE FROM example WHERE rowid = 2;",
            &insert_900byte_stmt_4,
            &insert_901byte_stmt_2,
            &insert_2000byte_stmt_5,
            "DELETE FROM example WHERE rowid = 2;",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        assert_eq!(bctx.max_local(false), 1002);
        let index_page_id = find_index_page_id("index1", file.path());

        let page = pager.get_page(index_page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        assert_eq!(page_header.first_freeblock_offset(), 1372);
        assert_eq!(page_header.fragmented_free_bytes(), 1);
        assert_eq!(page_header.cell_content_area_offset().get(), 877);
        assert_eq!(
            FreeblockIterator::new(page_header.first_freeblock_offset(), &buffer)
                .next()
                .unwrap(),
            (1372, 908)
        );
        drop(buffer);

        let mut cursor = BtreeCursor::new(index_page_id, &pager, &bctx).unwrap();

        let rowid_value = Value::Integer(6);
        let value = Value::Blob(vec![0x66; 902].into());
        let payload6 = build_record(&[Some(&value), Some(&rowid_value)]);
        let comparator = [
            Some(ValueCmp::new(&value, &Collation::Binary)),
            Some(ValueCmp::new(&rowid_value, &Collation::Binary)),
        ];
        cursor
            .index_insert(&comparator, &SlicePayload::new(&payload6).unwrap())
            .unwrap();

        let page = pager.get_page(index_page_id).unwrap();
        let buffer = page.buffer();
        let page_header = BtreePageHeader::from_page(&page, &buffer);
        assert_eq!(page_header.first_freeblock_offset(), 0);
        assert_eq!(page_header.fragmented_free_bytes(), 0);
        assert_eq!(page_header.cell_content_area_offset().get(), 877);
        drop(buffer);

        cursor.move_to_first().unwrap();

        let payload3 = build_record(&[
            Some(&Value::Blob([0x33; 901].as_slice().into())),
            Some(&Value::Integer(3)),
        ]);
        let payload4 = build_record(&[
            Some(&Value::Blob([0x44; 900].as_slice().into())),
            Some(&Value::Integer(4)),
        ]);
        let payload5 = build_record(&[
            Some(&Value::Blob([0x55; 2000].as_slice().into())),
            Some(&Value::Integer(5)),
        ]);
        assert_all_local_in_index_cursor(
            &mut cursor,
            &[
                &payload3,
                &payload4,
                &payload5
                    [..bctx.n_local(false, (payload5.len() as u64).try_into().unwrap()) as usize],
                &payload6,
            ],
        );
    }

    #[test]
    fn test_insert_index_split() {
        let file = create_sqlite_database(&[
            "PRAGMA page_size = 512;",
            "CREATE TABLE example(col);",
            "CREATE INDEX index1 ON example(col);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        assert_eq!(bctx.max_local(false), 102);
        let page_id = find_index_page_id("index1", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();
        for i in 0..1000 {
            let rowid_value = Value::Integer(i);
            let mut buf = (i as u16).to_be_bytes().to_vec();
            buf.extend(&[(i % 256) as u8; 90]);
            let value = Value::Blob(buf.into());
            let payload = build_record(&[Some(&value), Some(&rowid_value)]);
            let comparator = [
                Some(ValueCmp::new(&value, &Collation::Binary)),
                Some(ValueCmp::new(&rowid_value, &Collation::Binary)),
            ];
            cursor
                .index_insert(&comparator, &SlicePayload::new(&payload).unwrap())
                .unwrap();
        }
        // Overflow payloads
        for i in 1000..2000 {
            let rowid_value = Value::Integer(i);
            let mut buf = (i as u16).to_be_bytes().to_vec();
            buf.extend(&[(i % 256) as u8; 1000]);
            let value = Value::Blob(buf.into());
            let payload = build_record(&[Some(&value), Some(&rowid_value)]);
            let comparator = [
                Some(ValueCmp::new(&value, &Collation::Binary)),
                Some(ValueCmp::new(&rowid_value, &Collation::Binary)),
            ];
            cursor
                .index_insert(&comparator, &SlicePayload::new(&payload).unwrap())
                .unwrap();
        }

        cursor.move_to_first().unwrap();
        for i in 0..1000 {
            let rowid_value = Value::Integer(i);
            let mut buf = (i as u16).to_be_bytes().to_vec();
            buf.extend(&[(i % 256) as u8; 90]);
            let value = Value::Blob(buf.into());
            let expected = build_record(&[Some(&value), Some(&rowid_value)]);
            let payload = cursor.get_index_payload().unwrap().unwrap();
            assert_eq!(payload.buf(), &expected, "i = {}", i);
            drop(payload);
            cursor.move_next().unwrap();
        }
        for i in 1000..2000 {
            let rowid_value = Value::Integer(i);
            let mut buf = (i as u16).to_be_bytes().to_vec();
            buf.extend(&[(i % 256) as u8; 1000]);
            let value = Value::Blob(buf.into());
            let expected = build_record(&[Some(&value), Some(&rowid_value)]);
            let payload = cursor.get_index_payload().unwrap().unwrap();
            assert_eq!(payload.size().get() as usize, expected.len());
            let mut buf = vec![0; expected.len() + 1];
            assert_eq!(payload.load(0, &mut buf).unwrap(), expected.len());
            assert_eq!(&buf[..expected.len()], &expected, "i = {}", i);
            drop(payload);
            cursor.move_next().unwrap();
        }
        assert!(cursor.get_index_payload().unwrap().is_none());
    }

    #[test]
    fn test_insert_index_split_reversed() {
        let file = create_sqlite_database(&[
            "PRAGMA page_size = 512;",
            "CREATE TABLE example(col);",
            "CREATE INDEX index1 ON example(col);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        assert_eq!(bctx.max_local(false), 102);
        let page_id = find_index_page_id("index1", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();
        for i in 0..1000 {
            let rowid = 1000 - i;
            let rowid_value = Value::Integer(rowid);
            let mut buf = (rowid as u16).to_be_bytes().to_vec();
            buf.extend(&[(rowid % 256) as u8; 90]);
            let value = Value::Blob(buf.into());
            let payload = build_record(&[Some(&value), Some(&rowid_value)]);
            let comparator = [
                Some(ValueCmp::new(&value, &Collation::Binary)),
                Some(ValueCmp::new(&rowid_value, &Collation::Binary)),
            ];
            cursor
                .index_insert(&comparator, &SlicePayload::new(&payload).unwrap())
                .unwrap();
        }

        cursor.move_to_first().unwrap();
        for i in 0..1000 {
            let rowid = i + 1;
            let rowid_value = Value::Integer(rowid);
            let mut buf = (rowid as u16).to_be_bytes().to_vec();
            buf.extend(&[(rowid % 256) as u8; 90]);
            let value = Value::Blob(buf.into());
            let expected = build_record(&[Some(&value), Some(&rowid_value)]);
            let payload = cursor.get_index_payload().unwrap().unwrap();
            assert_eq!(payload.buf(), &expected, "i = {}", i);
            drop(payload);
            cursor.move_next().unwrap();
        }
        assert!(cursor.get_index_payload().unwrap().is_none());
    }

    #[test]
    fn test_insert_index_split_holes() {
        let file = create_sqlite_database(&[
            "PRAGMA page_size = 512;",
            "CREATE TABLE example(col);",
            "CREATE INDEX index1 ON example(col);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        assert_eq!(bctx.max_local(false), 102);
        let page_id = find_index_page_id("index1", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();
        for i in 0..4 {
            for j in 0..1000 {
                let rowid = 4 * j + i;
                let rowid_value = Value::Integer(rowid);
                let mut buf = (rowid as u16).to_be_bytes().to_vec();
                buf.extend(&[(rowid % 256) as u8; 90]);
                let value = Value::Blob(buf.into());
                let payload = build_record(&[Some(&value), Some(&rowid_value)]);
                let comparator = [
                    Some(ValueCmp::new(&value, &Collation::Binary)),
                    Some(ValueCmp::new(&rowid_value, &Collation::Binary)),
                ];
                cursor
                    .index_insert(&comparator, &SlicePayload::new(&payload).unwrap())
                    .unwrap();
            }
        }

        cursor.move_to_first().unwrap();
        for i in 0..4000 {
            let rowid = i;
            let rowid_value = Value::Integer(rowid);
            let mut buf = (rowid as u16).to_be_bytes().to_vec();
            buf.extend(&[(rowid % 256) as u8; 90]);
            let value = Value::Blob(buf.into());
            let expected = build_record(&[Some(&value), Some(&rowid_value)]);
            let payload = cursor.get_index_payload().unwrap().unwrap();
            assert_eq!(payload.buf(), &expected, "i = {}", i);
            drop(payload);
            cursor.move_next().unwrap();
        }
        assert!(cursor.get_index_payload().unwrap().is_none());
    }

    #[test]
    fn test_clear() {
        let mut stmts = vec![
            "PRAGMA page_size = 512;",
            "CREATE TABLE example(col);",
            "CREATE INDEX index1 ON example(col);",
        ];
        let insert_stmt = format!("INSERT INTO example(col) VALUES (x'{}');", "11".repeat(100));
        for _ in 0..1000 {
            stmts.push(&insert_stmt);
        }
        let file = create_sqlite_database(&stmts);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());
        let index_page_id = find_index_page_id("index1", file.path());

        let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();

        assert_eq!(cursor.clear().unwrap(), 1000);
        assert!(cursor.get_table_payload().unwrap().is_none());
        assert!(pager.num_free_pages() > 0);
        let n_free_pages_table = pager.num_free_pages();

        cursor.move_to_first().unwrap();
        assert!(cursor.get_table_payload().unwrap().is_none());

        assert_eq!(cursor.clear().unwrap(), 0);

        let mut cursor = BtreeCursor::new(index_page_id, &pager, &bctx).unwrap();

        assert_eq!(cursor.clear().unwrap(), 1000);
        assert!(cursor.get_index_payload().unwrap().is_none());
        assert!(pager.num_free_pages() > n_free_pages_table);

        cursor.move_to_first().unwrap();
        assert!(cursor.get_index_payload().unwrap().is_none());

        assert_eq!(cursor.clear().unwrap(), 0);
    }

    #[test]
    fn test_clear_single_leaf_page() {
        let mut stmts = vec![
            "PRAGMA page_size = 512;",
            "CREATE TABLE example(col);",
            "CREATE INDEX index1 ON example(col);",
        ];
        stmts.resize(stmts.len() + 10, "INSERT INTO example(col) VALUES (10);");
        let file = create_sqlite_database(&stmts);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());
        let index_page_id = find_index_page_id("index1", file.path());

        let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();

        assert_eq!(cursor.clear().unwrap(), 10);
        assert!(cursor.get_table_payload().unwrap().is_none());

        cursor.move_to_first().unwrap();
        assert!(cursor.get_table_payload().unwrap().is_none());
        assert_eq!(pager.num_free_pages(), 0);

        let mut cursor = BtreeCursor::new(index_page_id, &pager, &bctx).unwrap();

        assert_eq!(cursor.clear().unwrap(), 10);
        assert!(cursor.get_index_payload().unwrap().is_none());

        cursor.move_to_first().unwrap();
        assert!(cursor.get_index_payload().unwrap().is_none());
        assert_eq!(pager.num_free_pages(), 0);
    }
}
