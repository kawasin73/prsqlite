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
use std::ptr::copy_nonoverlapping;

use anyhow::bail;

use crate::btree::parse_btree_interior_cell_page_id;
use crate::btree::parse_btree_leaf_table_cell;
use crate::btree::BtreeContext;
use crate::btree::BtreePageHeader;
use crate::btree::PayloadInfo;
use crate::btree::TableCellKeyParser;
use crate::pager::MemPage;
use crate::pager::PageBuffer;
use crate::pager::PageId;
use crate::pager::Pager;

pub struct BtreePayload<'a, 'pager> {
    pager: &'pager Pager,
    local_payload_buffer: PageBuffer<'a>,
    payload_info: PayloadInfo,
}

impl<'a, 'pager> BtreePayload<'a, 'pager> {
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
    ///
    /// # Safety
    ///
    /// The buffer must not be any [MemPage] buffer.
    pub unsafe fn load(&self, offset: i32, buf: &mut [u8]) -> anyhow::Result<usize> {
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

            // SAFETY: n is less than buf.len() and payload.len().
            // SAFETY: payload and buf do not overlap.
            unsafe {
                copy_nonoverlapping(payload[local_offset..].as_ptr(), buf.as_mut_ptr(), n);
            }
            n_loaded += n;
            offset += n as i32;
            buf = &mut buf[n..];
        }

        let mut cur = payload.len() as i32;
        let mut overflow = self.payload_info.overflow;
        while !buf.is_empty() && cur < self.payload_info.payload_size {
            let overflow_page = overflow.ok_or_else(|| anyhow::anyhow!("overflow page is not found"))?;
            let page = self.pager.get_page(overflow_page.page_id())?;
            let buffer = page.buffer();
            let (payload, next_overflow) = overflow_page
                .parse(&buffer)
                .map_err(|e| anyhow::anyhow!("parse overflow: {:?}", e))?;
            if offset < cur + payload.len() as i32 {
                let local_offset = (offset - cur) as usize;
                let n = std::cmp::min(payload.len() - local_offset, buf.len());

                // SAFETY: n is less than buf.len() and payload.len().
                // SAFETY: payload and buf do not overlap.
                unsafe {
                    copy_nonoverlapping(payload[local_offset..].as_ptr(), buf.as_mut_ptr(), n);
                }
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

pub struct BtreeCursor<'ctx, 'pager> {
    pager: &'pager Pager,
    btree_ctx: &'ctx BtreeContext,
    current_page_id: PageId,
    current_page: MemPage,
    idx_cell: u16,
    parent_pages: Vec<(PageId, u16)>,
    initialized: bool,
}

impl<'ctx, 'pager> BtreeCursor<'ctx, 'pager> {
    pub fn new(root_page: PageId, pager: &'pager Pager, btree_ctx: &'ctx BtreeContext) -> anyhow::Result<Self> {
        Ok(Self {
            pager,
            btree_ctx,
            current_page_id: root_page,
            current_page: pager.get_page(root_page)?,
            idx_cell: 0,
            parent_pages: Vec::new(),
            initialized: false,
        })
    }

    /// Move to the specified cell with the key.
    ///
    /// If it does not exist, move to the next cell.
    pub fn move_to(&mut self, key: i64) -> anyhow::Result<()> {
        // TODO: optimize for sequential access. i.e. key == previouse key + 1
        self.move_to_root()?;
        loop {
            let buffer = self.current_page.buffer();
            let page_header = BtreePageHeader::from_page(&self.current_page, &buffer);
            let n_cells = page_header.n_cells();
            let mut i_min = 0;
            let mut i_max = n_cells as usize;
            let cell_key_parser = TableCellKeyParser::new(&self.current_page, &buffer);

            while i_min < i_max {
                let i_mid = (i_min + i_max) / 2;
                let cell_key = cell_key_parser
                    .get_cell_key(i_mid as u16)
                    .map_err(|e| anyhow::anyhow!("parse table cell key: {:?}", e))?;
                match cell_key.cmp(&key) {
                    Ordering::Less => {
                        i_min = i_mid + 1;
                    }
                    Ordering::Equal => {
                        i_min = i_mid;
                        break;
                    }
                    Ordering::Greater => {
                        i_max = i_mid;
                    }
                }
            }
            self.idx_cell = i_min as u16;
            if page_header.is_leaf() {
                self.initialized = true;
                return Ok(());
            }

            let next_page_id = if i_min == n_cells as usize {
                page_header.right_page_id()
            } else {
                parse_btree_interior_cell_page_id(&self.current_page, &buffer, self.idx_cell)
                    .map_err(|e| anyhow::anyhow!("get btree interior cell page id: {:?}", e))?
            };
            drop(buffer);
            self.move_to_child(next_page_id)?;
        }
    }

    pub fn move_to_first(&mut self) -> anyhow::Result<()> {
        self.move_to_root()?;
        self.idx_cell = 0;
        let buffer = self.current_page.buffer();
        let page_header = BtreePageHeader::from_page(&self.current_page, &buffer);
        if !page_header.is_leaf() {
            drop(buffer);
            self.move_to_left_most()?;
        }
        self.initialized = true;
        Ok(())
    }

    pub fn next(&mut self) -> anyhow::Result<()> {
        if !self.initialized {
            bail!("cursor is not initialized");
        }
        let buffer = self.current_page.buffer();
        let page_header = BtreePageHeader::from_page(&self.current_page, &buffer);
        let n_cells = page_header.n_cells();
        let is_leaf = page_header.is_leaf();
        drop(buffer);
        if !is_leaf {
            // If the the page is interior page, it means that it is the root page.
            assert!(self.parent_pages.is_empty());
            // If idx_cell is not 0, it means that the cursor is completed and
            // `self.idx_cell == page_header.n_cells() + 1`.
            assert_eq!(self.idx_cell, n_cells + 2);
        } else {
            self.idx_cell += 1;
            if self.idx_cell == n_cells {
                loop {
                    if !self.back_to_parent()? {
                        self.idx_cell += 1;
                        break;
                    }
                    self.idx_cell += 1;
                    if self.move_to_left_most()? {
                        break;
                    }
                }
            }
        }
        Ok(())
    }

    pub fn get_table_payload<'a>(&'a self) -> anyhow::Result<Option<(i64, BtreePayload<'a, 'pager>)>> {
        if !self.initialized {
            bail!("cursor is not initialized");
        }
        let buffer = self.current_page.buffer();
        let page_header = BtreePageHeader::from_page(&self.current_page, &buffer);
        assert!(page_header.is_table());
        assert!(!page_header.is_index());
        if self.idx_cell >= page_header.n_cells() {
            return Ok(None);
        }
        let (key, payload_info) =
            parse_btree_leaf_table_cell(self.btree_ctx, &self.current_page, &buffer, self.idx_cell)
                .map_err(|e| anyhow::anyhow!("parse tree leaf table cell: {:?}", e))?;
        return Ok(Some((
            key,
            BtreePayload {
                pager: self.pager,
                local_payload_buffer: self.current_page.buffer(),
                payload_info,
            },
        )));
    }

    /// Move to the left most cell in its child and grand child page.
    ///
    /// The cursor must points to a interior page.
    /// If cursor is completed, return `Ok(false)`.
    fn move_to_left_most(&mut self) -> anyhow::Result<bool> {
        let buffer = self.current_page.buffer();
        let page_header = BtreePageHeader::from_page(&self.current_page, &buffer);
        assert!(!page_header.is_leaf());
        let page_id = match self.idx_cell.cmp(&page_header.n_cells()) {
            Ordering::Less => parse_btree_interior_cell_page_id(&self.current_page, &buffer, self.idx_cell)
                .map_err(|e| anyhow::anyhow!("get btree interior cell page id: {:?}", e))?,
            Ordering::Equal => page_header.right_page_id(),
            Ordering::Greater => {
                // The cursor traversed all cells in the interior page.
                return Ok(false);
            }
        };
        drop(buffer);
        self.move_to_child(page_id)?;
        self.idx_cell = 0;
        loop {
            let buffer = self.current_page.buffer();
            let page_header = BtreePageHeader::from_page(&self.current_page, &buffer);
            if page_header.is_leaf() {
                break;
            }
            let page_id = parse_btree_interior_cell_page_id(&self.current_page, &buffer, 0)
                .map_err(|e| anyhow::anyhow!("get btree interior cell page id: {:?}", e))?;
            drop(buffer);
            self.move_to_child(page_id)?;
        }
        Ok(true)
    }

    fn move_to_root(&mut self) -> anyhow::Result<()> {
        if !self.parent_pages.is_empty() {
            self.current_page_id = self.parent_pages[0].0;
            self.current_page = self.pager.get_page(self.current_page_id)?;
            self.parent_pages.truncate(0);
        }
        Ok(())
    }

    fn move_to_child(&mut self, page_id: PageId) -> anyhow::Result<()> {
        self.parent_pages.push((self.current_page_id, self.idx_cell));
        self.current_page_id = page_id;
        self.current_page = self.pager.get_page(self.current_page_id)?;
        Ok(())
    }

    fn back_to_parent(&mut self) -> anyhow::Result<bool> {
        let (page_id, idx_cell) = match self.parent_pages.pop() {
            Some((page_id, idx_cell)) => (page_id, idx_cell),
            None => {
                return Ok(false);
            }
        };
        self.current_page_id = page_id;
        self.current_page = self.pager.get_page(self.current_page_id)?;
        self.idx_cell = idx_cell;
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::test_utils::*;

    #[test]
    fn test_btree_cursor_single_page() {
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
        drop(payload);

        cursor.next().unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_some());
        let (key, payload) = payload.unwrap();
        assert_eq!(key, 2);
        assert_eq!(payload.buf(), &[2, 9]);
        assert_eq!(payload.size(), payload.buf().len() as i32);
        drop(payload);

        cursor.next().unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_some());
        let (key, payload) = payload.unwrap();
        assert_eq!(key, 3);
        assert_eq!(payload.buf(), &[2, 1, 2]);
        assert_eq!(payload.size(), payload.buf().len() as i32);
        drop(payload);

        cursor.next().unwrap();
        assert!(cursor.get_table_payload().unwrap().is_none());
    }

    #[test]
    fn test_cursor_uninitialized() {
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

        assert!(cursor.next().is_err());
        assert!(cursor.get_table_payload().is_err());
    }

    #[test]
    fn test_btree_cursor_empty_records() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();
        cursor.move_to_first().unwrap();
        assert!(cursor.get_table_payload().unwrap().is_none());
        cursor.next().unwrap();
        assert!(cursor.get_table_payload().unwrap().is_none());
    }

    #[test]
    fn test_btree_cursor_multiple_page() {
        let buf = vec![0; 4000];
        let hex = buffer_to_hex(&buf);
        let mut inserts = Vec::new();
        // 1000 byte blob entry occupies 1 page. These 2000 entries introduce
        // 2 level interior pages and 1 leaf page level.
        for i in 0..1000 {
            inserts.push(format!(
                "INSERT INTO example(col,buf) VALUES ({},X'{}');",
                i,
                hex.as_str()
            ));
        }
        for i in 0..1000 {
            inserts.push(format!("INSERT INTO example(col) VALUES ({});", i % 100 + 2));
        }
        let mut queries = vec!["CREATE TABLE example(col,buf);"];
        queries.extend(inserts.iter().map(|s| s.as_str()));
        let file = create_sqlite_database(&queries);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();
        cursor.move_to_first().unwrap();

        for _ in 0..1000 {
            let payload = cursor.get_table_payload().unwrap();
            assert!(payload.is_some());
            let (_, payload) = payload.unwrap();
            assert!(payload.size() > 4000);
            assert_eq!(payload.size(), payload.buf().len() as i32);
            drop(payload);
            cursor.next().unwrap();
        }
        for i in 0..1000 {
            let payload = cursor.get_table_payload().unwrap();
            assert!(payload.is_some());
            let (_, payload) = payload.unwrap();
            assert_eq!(payload.buf(), &[3, 1, 0, ((i % 100) + 2) as u8]);
            assert_eq!(payload.size(), payload.buf().len() as i32);
            drop(payload);
            cursor.next().unwrap();
        }

        assert!(cursor.get_table_payload().unwrap().is_none());
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
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();
        cursor.move_to_first().unwrap();

        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_some());
        let (_, payload) = payload.unwrap();

        assert_eq!(payload.buf().len(), 1820);
        assert_eq!(payload.size(), 10004);

        let mut payload_buf = Vec::with_capacity(10010);
        unsafe {
            payload_buf.set_len(10010);
        }
        let n = unsafe { payload.load(0, &mut payload_buf) }.unwrap();
        assert_eq!(n, 10004);
        assert_eq!(payload_buf[0..4], [0x04, 0x81, 0x9c, 0x2c]);
        assert_eq!(&payload_buf[..payload.buf().len()], payload.buf());
        assert_eq!(payload_buf[4..10004], buf);

        let n = unsafe { payload.load(3000, &mut payload_buf) }.unwrap();
        assert_eq!(n, 7004);
        assert_eq!(payload_buf[..7004], buf[2996..]);

        let n = unsafe { payload.load(104, &mut payload_buf[..100]) }.unwrap();
        assert_eq!(n, 100);
        assert_eq!(payload_buf[..100], buf[100..200]);

        let n = unsafe { payload.load(3000, &mut payload_buf[..100]) }.unwrap();
        assert_eq!(n, 100);
        assert_eq!(payload_buf[..100], buf[2996..3096]);

        let result = unsafe { payload.load(10004, &mut payload_buf) };
        assert!(result.is_err());
    }

    #[test]
    fn test_move_to_in_single_page() {
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
            cursor.move_to(2 * i).unwrap();
            let payload = cursor.get_table_payload().unwrap();
            assert!(payload.is_some());
            let (key, _) = payload.unwrap();
            assert_eq!(key, 2 * i + 1);

            cursor.move_to(2 * i + 1).unwrap();
            let payload = cursor.get_table_payload().unwrap();
            assert!(payload.is_some());
            let (key, _) = payload.unwrap();
            assert_eq!(key, 2 * i + 1);
        }

        cursor.move_to(16).unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_none());
    }

    #[test]
    fn test_move_to_empty_rows() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();

        for i in 0..3 {
            cursor.move_to(i).unwrap();
            let payload = cursor.get_table_payload().unwrap();
            assert!(payload.is_none());
        }
    }

    #[test]
    fn test_move_to_multiple_page() {
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
            inserts.push(format!("INSERT INTO example(rowid) VALUES ({});", 2 * i + 1));
        }
        let mut queries = vec!["CREATE TABLE example(col);"];
        queries.extend(inserts.iter().map(|s| s.as_str()));
        let file = create_sqlite_database(&queries);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let page_id = find_table_page_id("example", file.path());

        let mut cursor = BtreeCursor::new(page_id, &pager, &bctx).unwrap();

        for i in 0..2000 {
            cursor.move_to(2 * i).unwrap();
            let payload = cursor.get_table_payload().unwrap();
            assert!(payload.is_some());
            let (key, _) = payload.unwrap();
            assert_eq!(key, 2 * i + 1);

            cursor.move_to(2 * i + 1).unwrap();
            let payload = cursor.get_table_payload().unwrap();
            assert!(payload.is_some());
            let (key, _) = payload.unwrap();
            assert_eq!(key, 2 * i + 1);
        }

        cursor.move_to(40002).unwrap();
        let payload = cursor.get_table_payload().unwrap();
        assert!(payload.is_none());
    }
}
