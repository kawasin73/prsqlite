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

use std::cell::BorrowError;
use std::cell::BorrowMutError;
use std::cell::Cell;
use std::cell::Ref;
use std::cell::RefCell;
use std::cell::RefMut;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fmt::Display;
use std::fs::File;
use std::io;
use std::num::NonZeroU32;
use std::ops::Deref;
use std::ops::DerefMut;
use std::os::unix::fs::FileExt;
use std::rc::Rc;

use crate::header::DatabaseHeader;
use crate::header::DatabaseHeaderMut;
use crate::header::DATABASE_HEADER_SIZE;
use crate::payload::CopiablePayload;
use crate::payload::PayloadSize;

/// Page 1 is special:
///
/// * It contains the database header.
/// * It is the root page of sqlite_schema table.
pub const PAGE_ID_1: PageId = NonZeroU32::MIN;
/// The maximum page size is 65536.
pub const MAX_PAGE_SIZE: usize = 65536;
/// The maximum page id is 4294967294.
const MAX_PAGE_ID: u32 = u32::MAX - 1;

/// Page id starts from 1.
pub type PageId = NonZeroU32;

#[derive(Debug)]
pub enum Error {
    Io(io::Error),
    InvalidFile,
    NoSpace,
    InvalidPageId,
    RemainingReference,
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(e) => Some(e),
            _ => None,
        }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(e) => f.write_fmt(format_args!("pager io: {}", e)),
            Self::InvalidFile => f.write_str("invalid file"),
            Self::NoSpace => f.write_str("no space"),
            Self::InvalidPageId => f.write_str("invalid page id"),
            Self::RemainingReference => f.write_str("remaining reference of dirty page"),
        }
    }
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

impl From<BorrowMutError> for Error {
    fn from(_: BorrowMutError) -> Self {
        Self::RemainingReference
    }
}

impl From<BorrowError> for Error {
    fn from(_: BorrowError) -> Self {
        Self::RemainingReference
    }
}

type Result<T> = std::result::Result<T, Error>;

pub struct TemporaryPage(Vec<u8>);

impl Deref for TemporaryPage {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for TemporaryPage {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// The size of a page is more than 512.
pub struct PageBuffer<'a>(Ref<'a, RawPage>);

impl<'a> Deref for PageBuffer<'a> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.0.buf
    }
}
pub struct PageBufferMut<'a>(RefMut<'a, RawPage>);

impl PageBufferMut<'_> {
    pub fn swap_tmp(&mut self, buffer: &mut TemporaryPage) {
        std::mem::swap(&mut self.0.buf, &mut buffer.0);
    }
}

impl<'a> Deref for PageBufferMut<'a> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.0.buf
    }
}

impl<'a> DerefMut for PageBufferMut<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0.buf
    }
}

pub fn swap_page_buffer(a: &mut PageBufferMut, b: &mut PageBufferMut) {
    std::mem::swap(&mut a.0.buf, &mut b.0.buf);
}

pub struct Pager {
    file: File,
    cache: PageCache,
    n_pages: Cell<u32>,
    n_pages_stable: Cell<u32>,
    first_freelist_trunk_page_id: Cell<Option<PageId>>,
    n_freelist_pages: Cell<u32>,
    usable_size: u32,
}

impl Pager {
    pub fn new(
        file: File,
        n_pages: u32,
        pagesize: u32,
        usable_size: u32,
        first_freelist_trunk_page_id: Option<PageId>,
        n_freelist_pages: u32,
    ) -> Result<Self> {
        if n_pages > MAX_PAGE_ID {
            return Err(Error::InvalidFile);
        }
        let file_len = file.metadata()?.len();
        if file_len % pagesize as u64 != 0 {
            todo!("file size mismatch");
        } else if file_len / (pagesize as u64) != n_pages as u64 {
            todo!("file size mismatch");
        }
        Ok(Self {
            file,
            cache: PageCache::new(pagesize),
            n_pages: Cell::new(n_pages),
            n_pages_stable: Cell::new(n_pages),
            first_freelist_trunk_page_id: Cell::new(first_freelist_trunk_page_id),
            n_freelist_pages: Cell::new(n_freelist_pages),
            usable_size,
        })
    }

    pub fn allocate_page(&self) -> Result<(PageId, MemPage)> {
        let page_id = if let Some(page_id) = self.allocate_from_freelist()? {
            page_id
        } else {
            let page_id = self.n_pages.get() + 1;
            if page_id > MAX_PAGE_ID {
                return Err(Error::NoSpace);
            }
            self.n_pages.set(page_id);
            PageId::new(page_id).unwrap()
        };

        let (page, _) = self.cache.get_page(page_id);
        page.try_borrow_mut()?.is_dirty = true;
        // TODO: setup journal

        let header_offset = if page_id == PAGE_ID_1 {
            DATABASE_HEADER_SIZE
        } else {
            0
        };
        Ok((
            page_id,
            MemPage {
                page,
                header_offset,
            },
        ))
    }

    fn allocate_from_freelist(&self) -> Result<Option<PageId>> {
        if let Some(first_page_id) = self.first_freelist_trunk_page_id.get() {
            let (page1, is_new) = self.cache.get_page(PAGE_ID_1);
            let mut page1 = if is_new {
                let mut page1 = page1.borrow_mut();
                self.file.read_exact_at(&mut page1.buf, 0)?;
                page1
            } else {
                page1.try_borrow_mut()?
            };
            page1.is_dirty = true;
            let buffer = &mut page1.buf;
            let mut header =
                DatabaseHeaderMut::from((&mut buffer[..DATABASE_HEADER_SIZE]).try_into().unwrap());

            let (trunk_page, is_new) = self.cache.get_page(first_page_id);
            let mut trunk_page = if is_new {
                let mut trunk_page = trunk_page.borrow_mut();
                self.file
                    .read_exact_at(&mut trunk_page.buf, self.page_offset(first_page_id))?;
                trunk_page
            } else {
                trunk_page.try_borrow_mut()?
            };
            let trunk_buffer = &mut trunk_page.buf;
            let n_pages = u32::from_be_bytes(trunk_buffer[4..8].try_into().unwrap());

            if n_pages > self.usable_size / 4 - 2 {
                return Err(Error::InvalidFile);
            }

            let page_id = if n_pages == 0 {
                self.first_freelist_trunk_page_id
                    .set(PageId::new(u32::from_be_bytes(
                        trunk_buffer[0..4].try_into().unwrap(),
                    )));
                header.set_first_freelist_trunk_page_id_raw(trunk_buffer[0..4].try_into().unwrap());
                first_page_id
            } else {
                let offset = (n_pages * 4) as usize + 4;
                let next_page_id = PageId::new(u32::from_be_bytes(
                    trunk_buffer[offset..offset + 4].try_into().unwrap(),
                ))
                .unwrap();
                trunk_buffer[4..8].copy_from_slice(&(n_pages - 1).to_be_bytes());
                next_page_id
            };

            if page_id.get() > self.n_pages.get() {
                return Err(Error::InvalidFile);
            }

            let n_freelist_pages = self.n_freelist_pages.get() - 1;
            self.n_freelist_pages.set(n_freelist_pages);
            header.set_n_freelist_pages(n_freelist_pages);

            Ok(Some(page_id))
        } else {
            Ok(None)
        }
    }

    pub fn allocate_tmp_page(&self) -> TemporaryPage {
        TemporaryPage(vec![0_u8; self.cache.pagesize as usize])
    }

    pub fn get_page(&self, page_id: PageId) -> Result<MemPage> {
        if page_id.get() > self.n_pages.get() {
            return Err(Error::InvalidPageId);
        }
        let (page, is_new) = self.cache.get_page(page_id);
        if is_new {
            let mut raw_page = page.borrow_mut();
            self.file
                .read_exact_at(&mut raw_page.buf, self.page_offset(page_id))?;
        }
        let header_offset = if page_id == PAGE_ID_1 {
            DATABASE_HEADER_SIZE
        } else {
            0
        };
        Ok(MemPage {
            page,
            header_offset,
        })
    }

    pub fn make_page_mut<'a>(&self, page: &'a MemPage) -> Result<PageBufferMut<'a>> {
        let mut raw_page = page.page.try_borrow_mut()?;

        if !raw_page.is_dirty {
            raw_page.is_dirty = true;
            // TODO: setup journal
        }

        Ok(PageBufferMut(raw_page))
    }

    /// Delete a page and add it to the freelist.
    ///
    /// TODO: Shrink the database file if the page is the tail.
    pub fn delete_page(&self, page_id: PageId) -> Result<()> {
        if page_id == PAGE_ID_1 || page_id.get() > self.n_pages.get() {
            return Err(Error::InvalidPageId);
        }
        let (page1, is_new) = self.cache.get_page(PAGE_ID_1);
        let mut page1 = if is_new {
            let mut page1 = page1.borrow_mut();
            self.file.read_exact_at(&mut page1.buf, 0)?;
            page1
        } else {
            page1.try_borrow_mut()?
        };
        page1.is_dirty = true;
        let buffer = &mut page1.buf;
        let mut header =
            DatabaseHeaderMut::from((&mut buffer[..DATABASE_HEADER_SIZE]).try_into().unwrap());

        self.n_freelist_pages.set(self.n_freelist_pages.get() + 1);
        header.set_n_freelist_pages(self.n_freelist_pages.get());

        if let Some(first_page_id) = self.first_freelist_trunk_page_id.get() {
            if first_page_id.get() > self.n_pages.get() {
                return Err(Error::InvalidFile);
            }
            let (trunk_page, is_new) = self.cache.get_page(first_page_id);
            let mut trunk_page = if is_new {
                let mut trunk_page = trunk_page.borrow_mut();
                self.file
                    .read_exact_at(&mut trunk_page.buf, self.page_offset(first_page_id))?;
                trunk_page
            } else {
                trunk_page.try_borrow_mut()?
            };
            // First 2 items in the array are the next freelist trunk page id and the number
            // of pages.
            let max_freelist_pages = self.usable_size / 4 - 2;
            let buffer = &mut trunk_page.buf;
            let n_pages = u32::from_be_bytes(buffer[4..8].try_into().unwrap());

            // We don't put page_id to the last 6 entries in a freelist trunk page due to a
            // bug in SQLite versions prior to 3.6.0 which reports as the file
            // is corrupt if there are any page_id in the last 6 entries.
            // https://www.sqlite.org/fileformat2.html#the_freelist
            if n_pages < max_freelist_pages - 6 {
                // Add the deleted page to the freelist trunk page.
                buffer[4..8].copy_from_slice(&(n_pages + 1).to_be_bytes());
                let offset = (n_pages * 4) as usize + 8;
                buffer[offset..offset + 4].copy_from_slice(&page_id.get().to_be_bytes());
                trunk_page.is_dirty = true;
                self.cache.delete_page(page_id);
                return Ok(());
            } else if n_pages > max_freelist_pages {
                return Err(Error::InvalidPageId);
            }
            // Fallthrough if the freelist trunk page is full.
        } else if self.n_freelist_pages.get() != 1 {
            return Err(Error::InvalidFile);
        }

        // Use the deleted page as a new freelist trunk page.
        let (deleted_page, _) = self.cache.get_page(page_id);
        let mut deleted_page = deleted_page.try_borrow_mut()?;
        deleted_page.is_dirty = true;
        deleted_page.buf[..4].copy_from_slice(
            &self
                .first_freelist_trunk_page_id
                .get()
                .map(PageId::get)
                .unwrap_or(0)
                .to_be_bytes(),
        );
        deleted_page.buf[4..8].fill(0);

        self.first_freelist_trunk_page_id.set(Some(page_id));
        header.set_first_freelist_trunk_page_id(Some(page_id));

        Ok(())
    }

    /// Commit all dirty pages.
    ///
    /// No reference to buffers of any dirty pages must be kept when commiting.
    pub fn commit(&self) -> Result<()> {
        for (page_id, page) in self.cache.map.borrow().iter() {
            let raw_page = page.try_borrow()?;
            if raw_page.is_dirty {
                self.file
                    .write_all_at(&raw_page.buf, self.page_offset(*page_id))?;
                drop(raw_page);
                page.try_borrow_mut()?.is_dirty = false;
            }
        }
        self.n_pages_stable.set(self.n_pages.get());
        Ok(())
    }

    pub fn abort(&self) {
        self.n_pages.set(self.n_pages_stable.get());

        // Drop all dirty pages.
        self.cache
            .map
            .borrow_mut()
            .retain(|_, page| !page.borrow().is_dirty);

        // Invalidate cached database header.
        if self.n_pages.get() > 0 {
            let (page1, is_new) = self.cache.get_page(PAGE_ID_1);
            if is_new {
                let mut page1 = page1.borrow_mut();
                self.file
                    .read_exact_at(&mut page1.buf, 0)
                    .expect("read page 1 must succeed");
            }
            let buffer = &page1.borrow().buf;
            let header = DatabaseHeader::from(buffer[..DATABASE_HEADER_SIZE].try_into().unwrap());
            self.first_freelist_trunk_page_id
                .set(header.first_freelist_trunk_page_id());
            self.n_freelist_pages.set(header.n_freelist_pages());
        } else {
            self.first_freelist_trunk_page_id.set(None);
            self.n_freelist_pages.set(0);
        }

        // TODO: rollback journal
    }

    pub fn is_file_size_changed(&self) -> bool {
        self.n_pages.get() != self.n_pages_stable.get()
    }

    pub fn num_pages(&self) -> u32 {
        self.n_pages.get()
    }

    /// The number of free pages in the database.
    ///
    /// This is used by test only.
    #[allow(dead_code)]
    pub fn num_free_pages(&self) -> u32 {
        self.n_freelist_pages.get()
    }

    #[inline]
    fn page_offset(&self, page_id: PageId) -> u64 {
        (page_id.get() - 1) as u64 * self.cache.pagesize as u64
    }
}

pub struct MemPage {
    page: Rc<RefCell<RawPage>>,
    pub header_offset: usize,
}

impl MemPage {
    #[inline(always)]
    pub fn buffer(&self) -> PageBuffer {
        PageBuffer(self.page.borrow())
    }
}

pub struct PagePayload {
    page: MemPage,
    offset: usize,
    size: PayloadSize,
}

impl PagePayload {
    pub fn new(page: &MemPage, offset: usize, size: PayloadSize) -> Self {
        let page = MemPage {
            page: page.page.clone(),
            header_offset: page.header_offset,
        };
        Self { page, offset, size }
    }
}

impl CopiablePayload for PagePayload {
    fn size(&self) -> PayloadSize {
        self.size
    }

    fn copy(&self, offset: usize, buf: &mut [u8]) -> usize {
        assert!(offset <= self.size.get() as usize);
        let n = buf.len().min(self.size.get() as usize - offset);
        buf[..n]
            .copy_from_slice(&self.page.buffer()[self.offset + offset..self.offset + offset + n]);
        n
    }
}

struct RawPage {
    buf: Vec<u8>,
    is_dirty: bool,
}

impl RawPage {
    fn new(pagesize: u32) -> Self {
        Self {
            buf: vec![0_u8; pagesize as usize],
            is_dirty: false,
        }
    }
}

struct PageCache {
    map: RefCell<HashMap<PageId, Rc<RefCell<RawPage>>>>,
    pagesize: u32,
}

impl PageCache {
    fn new(pagesize: u32) -> Self {
        Self {
            map: RefCell::new(HashMap::new()),
            pagesize,
        }
    }

    fn get_page(&self, id: PageId) -> (Rc<RefCell<RawPage>>, bool) {
        match self.map.borrow_mut().entry(id) {
            Entry::Occupied(entry) => (entry.get().clone(), false),
            Entry::Vacant(entry) => {
                let page = Rc::new(RefCell::new(RawPage::new(self.pagesize)));
                entry.insert(page.clone());
                (page, true)
            }
        }
    }

    fn delete_page(&self, id: PageId) {
        self.map.borrow_mut().remove(&id);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::create_empty_pager;

    #[test]
    fn test_new() {
        let file = tempfile::tempfile().unwrap();
        file.write_all_at(&[0_u8; 4096], 0).unwrap();
        let pager = Pager::new(file, 1, 4096, 4096, None, 0).unwrap();
        assert_eq!(pager.num_pages(), 1);

        let file = tempfile::tempfile().unwrap();
        file.write_all_at(&[0_u8; 4096 * 2], 0).unwrap();
        let pager = Pager::new(file, 2, 4096, 4096, None, 0).unwrap();
        assert_eq!(pager.num_pages(), 2);

        let file = tempfile::tempfile().unwrap();
        assert!(matches!(
            Pager::new(file, u32::MAX, 4096, 4096, None, 0)
                .err()
                .unwrap(),
            Error::InvalidFile
        ));
    }

    #[test]
    fn test_get_page() {
        let file = tempfile::tempfile().unwrap();
        file.write_all_at(&[1_u8; 4096], 0).unwrap();
        file.write_all_at(&[2_u8; 4096], 4096).unwrap();
        let pager = Pager::new(file, 2, 4096, 4096, None, 0).unwrap();

        let page = pager.get_page(PAGE_ID_1).unwrap();
        let buffer = page.buffer();
        assert_eq!(buffer.deref(), [1_u8; 4096].as_slice());
        assert_eq!(page.header_offset, DATABASE_HEADER_SIZE);

        let page = pager.get_page(PageId::new(2).unwrap()).unwrap();
        let buffer = page.buffer();
        assert_eq!(buffer.deref(), [2_u8; 4096].as_slice());
        assert_eq!(page.header_offset, 0);

        assert!(matches!(
            pager.get_page(PageId::new(3).unwrap()).err().unwrap(),
            Error::InvalidPageId
        ));
    }

    #[test]
    fn test_make_page_mut() {
        let file = tempfile::tempfile().unwrap();
        file.write_all_at(&[1_u8; 4096], 0).unwrap();
        file.write_all_at(&[2_u8; 4096], 4096).unwrap();
        let pager = Pager::new(file, 2, 4096, 4096, None, 0).unwrap();

        let page = pager.get_page(PAGE_ID_1).unwrap();
        let mut buffer = pager.make_page_mut(&page).unwrap();
        buffer[0] = 3;
        buffer[1] = 4;
        drop(buffer);
        let page = pager.get_page(PAGE_ID_1).unwrap();
        let buffer = page.buffer();
        assert_eq!(buffer[0], 3);
        assert_eq!(buffer[1], 4);

        let page_id_2 = PageId::new(2).unwrap();
        let page = pager.get_page(page_id_2).unwrap();
        let mut buffer = pager.make_page_mut(&page).unwrap();
        buffer[0] = 5;
        buffer[1] = 6;
        drop(buffer);
        let page = pager.get_page(page_id_2).unwrap();
        let buffer = page.buffer();
        assert_eq!(buffer[0], 5);
        assert_eq!(buffer[1], 6);

        assert!(!pager.is_file_size_changed());
    }

    #[test]
    fn test_make_page_mut_failure() {
        let file = tempfile::tempfile().unwrap();
        file.write_all_at(&[1_u8; 4096], 0).unwrap();
        let pager = Pager::new(file, 1, 4096, 4096, None, 0).unwrap();

        let page = pager.get_page(PAGE_ID_1).unwrap();
        // Immutable reference
        let buffer = page.buffer();
        assert!(matches!(
            pager.make_page_mut(&page).err().unwrap(),
            Error::RemainingReference
        ));

        drop(buffer);
        // Mutable reference
        let _buffer = pager.make_page_mut(&page).unwrap();
        assert!(matches!(
            pager.make_page_mut(&page).err().unwrap(),
            Error::RemainingReference
        ));
    }

    #[test]
    fn test_swap_page_buffer() {
        let file = tempfile::tempfile().unwrap();
        file.write_all_at(&[1_u8; 4096], 0).unwrap();
        file.write_all_at(&[2_u8; 4096], 4096).unwrap();
        let pager = Pager::new(file, 2, 4096, 4096, None, 0).unwrap();
        let page_id_2 = PageId::new(2).unwrap();

        let page1 = pager.get_page(PAGE_ID_1).unwrap();
        let mut buffer1 = pager.make_page_mut(&page1).unwrap();

        let page2 = pager.get_page(page_id_2).unwrap();
        let mut buffer2 = pager.make_page_mut(&page2).unwrap();

        assert_eq!(buffer1.deref(), [1_u8; 4096].as_slice());
        assert_eq!(buffer2.deref(), [2_u8; 4096].as_slice());

        swap_page_buffer(&mut buffer1, &mut buffer2);
        assert_eq!(buffer1.deref(), [2_u8; 4096].as_slice());
        assert_eq!(buffer2.deref(), [1_u8; 4096].as_slice());

        drop(buffer1);
        drop(buffer2);
        drop(page1);
        drop(page2);

        let page1 = pager.get_page(PAGE_ID_1).unwrap();
        let buffer1 = page1.buffer();
        let page2 = pager.get_page(page_id_2).unwrap();
        let buffer2 = page2.buffer();
        assert_eq!(buffer1.deref(), [2_u8; 4096].as_slice());
        assert_eq!(buffer2.deref(), [1_u8; 4096].as_slice());
    }

    #[test]
    fn test_commit() {
        let file = tempfile::NamedTempFile::new().unwrap();
        file.as_file().write_all_at(&[1_u8; 4096], 0).unwrap();
        file.as_file().write_all_at(&[2_u8; 4096], 4096).unwrap();
        let pager = Pager::new(file.reopen().unwrap(), 2, 4096, 4096, None, 0).unwrap();

        let page = pager.get_page(PAGE_ID_1).unwrap();
        let mut buffer = pager.make_page_mut(&page).unwrap();
        buffer.fill(3);
        drop(buffer);

        let page_id_2 = PageId::new(2).unwrap();
        let page = pager.get_page(page_id_2).unwrap();
        let mut buffer = pager.make_page_mut(&page).unwrap();
        buffer.fill(4);
        drop(buffer);

        pager.commit().unwrap();

        let mut buf = [0; 4096 * 2];
        file.as_file().read_exact_at(&mut buf, 0).unwrap();
        assert_eq!(buf[..4096], [3_u8; 4096]);
        assert_eq!(buf[4096..], [4_u8; 4096]);
    }

    #[test]
    fn test_commit_failure() {
        let file = tempfile::tempfile().unwrap();
        file.write_all_at(&[1_u8; 4096], 0).unwrap();
        let pager = Pager::new(file, 1, 4096, 4096, None, 0).unwrap();

        let page = pager.get_page(PAGE_ID_1).unwrap();
        let mut buffer = pager.make_page_mut(&page).unwrap();
        buffer.fill(3);
        // Without dropping buffer

        assert!(matches!(
            pager.commit().err().unwrap(),
            Error::RemainingReference
        ));
    }

    #[test]
    fn test_abort() {
        let file = tempfile::NamedTempFile::new().unwrap();
        let mut original = [1_u8; 4096];
        let mut header =
            DatabaseHeaderMut::from((&mut original[..DATABASE_HEADER_SIZE]).try_into().unwrap());
        header.set_first_freelist_trunk_page_id(PageId::new(2));
        header.set_n_freelist_pages(1);
        file.as_file().write_all_at(&original, 0).unwrap();
        let pager = Pager::new(file.reopen().unwrap(), 1, 4096, 4096, None, 0).unwrap();

        let page = pager.get_page(PAGE_ID_1).unwrap();
        let mut buffer = pager.make_page_mut(&page).unwrap();
        buffer.fill(3);
        drop(buffer);
        pager.n_freelist_pages.set(100);
        pager.first_freelist_trunk_page_id.set(PageId::new(10));

        pager.abort();

        assert_eq!(
            pager.get_page(PAGE_ID_1).unwrap().buffer().deref(),
            original.as_slice()
        );
        let mut buf = [0; 4096];
        file.as_file().read_exact_at(&mut buf, 0).unwrap();
        assert_eq!(buf, original);

        assert_eq!(pager.first_freelist_trunk_page_id.get(), PageId::new(2));
        assert_eq!(pager.n_freelist_pages.get(), 1);
    }

    #[test]
    fn test_allocate_page() {
        let file = tempfile::NamedTempFile::new().unwrap();
        let pager = Pager::new(file.reopen().unwrap(), 0, 4096, 4096, None, 0).unwrap();
        assert_eq!(pager.num_pages(), 0);
        assert_eq!(file.as_file().metadata().unwrap().len(), 0);

        let (page_id, page) = pager.allocate_page().unwrap();
        assert_eq!(pager.num_pages(), 1);
        assert!(pager.is_file_size_changed());
        assert_eq!(page_id, PAGE_ID_1);
        let mut buffer = pager.make_page_mut(&page).unwrap();
        buffer.fill(10);
        drop(buffer);

        let (page_id, page) = pager.allocate_page().unwrap();
        assert_eq!(pager.num_pages(), 2);
        assert!(pager.is_file_size_changed());
        assert_eq!(page_id.get(), 2);
        let mut buffer = pager.make_page_mut(&page).unwrap();
        buffer.fill(11);
        drop(buffer);

        assert_eq!(
            pager.get_page(PAGE_ID_1).unwrap().buffer().deref(),
            [10_u8; 4096].as_slice()
        );
        assert_eq!(
            pager
                .get_page(PageId::new(2).unwrap())
                .unwrap()
                .buffer()
                .deref(),
            [11_u8; 4096].as_slice()
        );

        pager.commit().unwrap();
        assert_eq!(pager.num_pages(), 2);
        assert!(!pager.is_file_size_changed());
        assert_eq!(file.as_file().metadata().unwrap().len(), 4096 * 2);

        let mut buf = [0; 4096 * 2];
        file.as_file().read_exact_at(&mut buf, 0).unwrap();
        assert_eq!(buf[..4096], [10_u8; 4096]);
        assert_eq!(buf[4096..], [11_u8; 4096]);
    }

    #[test]
    fn test_allocate_page_non_empty_file() {
        let file = tempfile::NamedTempFile::new().unwrap();
        file.as_file().write_all_at(&[1_u8; 4096], 0).unwrap();
        file.as_file().write_all_at(&[2_u8; 4096], 4096).unwrap();
        let pager = Pager::new(file.reopen().unwrap(), 2, 4096, 4096, None, 0).unwrap();

        let (page_id, page) = pager.allocate_page().unwrap();
        assert_eq!(pager.num_pages(), 3);
        assert!(pager.is_file_size_changed());
        assert_eq!(page_id.get(), 3);
        let mut buffer = pager.make_page_mut(&page).unwrap();
        buffer.fill(3);
        drop(buffer);

        pager.commit().unwrap();
        assert_eq!(pager.num_pages(), 3);
        assert!(!pager.is_file_size_changed());
        assert_eq!(file.as_file().metadata().unwrap().len(), 4096 * 3);

        let mut buf = [0; 4096 * 3];
        file.as_file().read_exact_at(&mut buf, 0).unwrap();
        assert_eq!(buf[..4096], [1_u8; 4096]);
        assert_eq!(buf[4096..4096 * 2], [2_u8; 4096]);
        assert_eq!(buf[4096 * 2..], [3_u8; 4096]);
    }

    #[test]
    fn test_allocate_page_failure() {
        let file = tempfile::NamedTempFile::new().unwrap();
        file.as_file()
            .write_all_at(&[1; 4096], (MAX_PAGE_ID as u64 - 1) * 4096)
            .unwrap();
        let pager = Pager::new(file.reopen().unwrap(), MAX_PAGE_ID, 4096, 4096, None, 0).unwrap();
        assert_eq!(pager.num_pages(), MAX_PAGE_ID);

        assert!(matches!(
            pager.allocate_page().err().unwrap(),
            Error::NoSpace
        ));
    }

    #[test]
    fn test_allocate_page_abort() {
        let file = tempfile::NamedTempFile::new().unwrap();
        file.as_file().write_all_at(&[1_u8; 4096], 0).unwrap();
        file.as_file().write_all_at(&[2_u8; 4096], 4096).unwrap();
        let pager = Pager::new(file.reopen().unwrap(), 2, 4096, 4096, None, 0).unwrap();

        let (page_id, page) = pager.allocate_page().unwrap();
        assert_eq!(pager.num_pages(), 3);
        assert!(pager.is_file_size_changed());
        assert_eq!(page_id.get(), 3);
        let mut buffer = pager.make_page_mut(&page).unwrap();
        buffer.fill(3);
        drop(buffer);

        let page = pager.get_page(PAGE_ID_1).unwrap();
        let mut buffer = pager.make_page_mut(&page).unwrap();
        buffer.fill(4);
        drop(buffer);

        pager.abort();
        assert_eq!(pager.num_pages(), 2);
        assert!(!pager.is_file_size_changed());
        assert_eq!(file.as_file().metadata().unwrap().len(), 4096 * 2);

        let mut buf = [0; 4096 * 2];
        file.as_file().read_exact_at(&mut buf, 0).unwrap();
        assert_eq!(buf[..4096], [1_u8; 4096]);
        assert_eq!(buf[4096..4096 * 2], [2_u8; 4096]);
    }

    fn assert_freelist_header(pager: &Pager, first_page_id: Option<PageId>, n_free_pages: u32) {
        let page1 = pager.get_page(PAGE_ID_1).unwrap();
        let buffer = page1.buffer();
        let header = DatabaseHeader::from((&buffer[..DATABASE_HEADER_SIZE]).try_into().unwrap());
        assert_eq!(header.first_freelist_trunk_page_id(), first_page_id);
        assert_eq!(header.n_freelist_pages(), n_free_pages);
    }

    #[test]
    fn test_allocate_page_from_freelist() {
        let file = tempfile::NamedTempFile::new().unwrap();
        let mut header_buf = [1; 4096];
        let mut header = DatabaseHeaderMut::from(
            (&mut header_buf[..DATABASE_HEADER_SIZE])
                .try_into()
                .unwrap(),
        );
        header.set_first_freelist_trunk_page_id(PageId::new(2));
        header.set_n_freelist_pages(5);
        file.as_file().write_all_at(&header_buf, 0).unwrap();
        file.as_file()
            .write_all_at(&[0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 5], 4096)
            .unwrap();
        file.as_file()
            .write_all_at(&[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 6], 4096 * 2)
            .unwrap();
        file.as_file().write_all_at(&[2; 4096], 4096 * 6).unwrap();
        let pager = Pager::new(file.reopen().unwrap(), 7, 4096, 4096, PageId::new(2), 5).unwrap();

        let (page_id, _) = pager.allocate_page().unwrap();
        assert_eq!(page_id.get(), 5);
        assert_freelist_header(&pager, PageId::new(2), 4);
        let (page_id, _) = pager.allocate_page().unwrap();
        assert_eq!(page_id.get(), 4);
        assert_freelist_header(&pager, PageId::new(2), 3);
        let (page_id, _) = pager.allocate_page().unwrap();
        assert_eq!(page_id.get(), 2);
        assert_freelist_header(&pager, PageId::new(3), 2);
        let (page_id, _) = pager.allocate_page().unwrap();
        assert_eq!(page_id.get(), 6);
        assert_freelist_header(&pager, PageId::new(3), 1);
        let (page_id, _) = pager.allocate_page().unwrap();
        assert_eq!(page_id.get(), 3);
        assert_freelist_header(&pager, None, 0);
        assert_eq!(pager.num_pages(), 7);
        // Extend new page.
        let (page_id, _) = pager.allocate_page().unwrap();
        assert_eq!(page_id.get(), 8);
        assert_eq!(pager.num_pages(), 8);
    }

    #[test]
    fn test_allocate_page_from_freelist_tail() {
        let file = tempfile::NamedTempFile::new().unwrap();
        let mut header_buf = [1; 512];
        let mut header = DatabaseHeaderMut::from(
            (&mut header_buf[..DATABASE_HEADER_SIZE])
                .try_into()
                .unwrap(),
        );
        header.set_first_freelist_trunk_page_id(PageId::new(2));
        header.set_n_freelist_pages(127);
        file.as_file().write_all_at(&header_buf, 0).unwrap();
        file.as_file()
            .write_all_at(&[0, 0, 0, 0, 0, 0, 0, 126], 512)
            .unwrap();
        file.as_file()
            .write_all_at(
                &[
                    0, 0, 0, 10, 0, 0, 0, 11, 0, 0, 0, 12, 0, 0, 0, 13, 0, 0, 0, 14, 0, 0, 0, 15,
                    0, 0, 0, 16, 0, 0, 0, 17, 0, 0, 0, 18,
                ],
                1024 - 36,
            )
            .unwrap();
        file.as_file().write_all_at(&[2; 512], 512 * 17).unwrap();
        let pager = Pager::new(file.reopen().unwrap(), 18, 512, 512, PageId::new(2), 127).unwrap();

        let (page_id, _) = pager.allocate_page().unwrap();
        assert_eq!(page_id.get(), 18);
        // Adjust n_free_pages.
        assert_freelist_header(&pager, PageId::new(2), 126);
        let (page_id, _) = pager.allocate_page().unwrap();
        assert_eq!(page_id.get(), 17);
        assert_freelist_header(&pager, PageId::new(2), 125);
        pager.abort();

        let pager = Pager::new(file.reopen().unwrap(), 18, 512, 510, PageId::new(2), 127).unwrap();
        // Usable size changes the capacity of the page. n_pages is reported as
        // corrupted.
        assert!(matches!(
            pager.allocate_page().err().unwrap(),
            Error::InvalidFile
        ));
    }

    #[test]
    fn test_delete_page() {
        let pager = create_empty_pager(&[0; 512], 512, 512);
        for i in 2..=300 {
            let (page_id, _) = pager.allocate_page().unwrap();
            assert_eq!(page_id.get(), i);
        }
        assert_eq!(pager.num_pages(), 300);
        pager.commit().unwrap();

        pager.delete_page(PageId::new(100).unwrap()).unwrap();
        pager.commit().unwrap();
        assert_eq!(pager.num_pages(), 300);

        let page1 = pager.get_page(PAGE_ID_1).unwrap();
        let buffer = page1.buffer();
        let header = DatabaseHeader::from((&buffer[..DATABASE_HEADER_SIZE]).try_into().unwrap());
        assert_eq!(
            header.first_freelist_trunk_page_id(),
            Some(PageId::new(100).unwrap())
        );
        assert_eq!(header.n_freelist_pages(), 1);
        drop(buffer);
        let page = pager.get_page(PageId::new(100).unwrap()).unwrap();
        let buffer = page.buffer();
        assert_eq!(&buffer[0..8], &[0; 8]);
        drop(buffer);

        for i in 101..200 {
            pager.delete_page(PageId::new(i).unwrap()).unwrap();
        }
        for i in 10..40 {
            pager.delete_page(PageId::new(i).unwrap()).unwrap();
        }
        pager.commit().unwrap();
        assert_eq!(pager.num_pages(), 300);

        let page1 = pager.get_page(PAGE_ID_1).unwrap();
        let buffer = page1.buffer();
        let header = DatabaseHeader::from((&buffer[..DATABASE_HEADER_SIZE]).try_into().unwrap());
        let first_page_id = header.first_freelist_trunk_page_id().unwrap();
        assert_eq!(first_page_id, PageId::new(31).unwrap());
        assert_eq!(header.n_freelist_pages(), 130);
        drop(buffer);
        let page = pager.get_page(first_page_id).unwrap();
        let buffer = page.buffer();
        let next_page_id = PageId::new(u32::from_be_bytes(buffer[0..4].try_into().unwrap()));
        assert_eq!(next_page_id, PageId::new(100));
        let n_free_pages = u32::from_be_bytes(buffer[4..8].try_into().unwrap());
        assert_eq!(n_free_pages, 8);
        for i in 0..n_free_pages {
            let offset = (i * 4) as usize + 8;
            assert_eq!(
                PageId::new(u32::from_be_bytes(
                    buffer[offset..offset + 4].try_into().unwrap()
                )),
                PageId::new(32 + i)
            );
        }
        let page = pager.get_page(next_page_id.unwrap()).unwrap();
        let buffer = page.buffer();
        let next_page_id = PageId::new(u32::from_be_bytes(buffer[0..4].try_into().unwrap()));
        assert_eq!(next_page_id, None);
        let n_free_pages = u32::from_be_bytes(buffer[4..8].try_into().unwrap());
        assert_eq!(n_free_pages, 120);
        for i in 0..99 {
            let offset = (i * 4) as usize + 8;
            // 101 ~ 199
            assert_eq!(
                PageId::new(u32::from_be_bytes(
                    buffer[offset..offset + 4].try_into().unwrap()
                )),
                PageId::new(101 + i)
            );
        }
        for i in 99..119 {
            let offset = (i * 4) as usize + 8;
            assert_eq!(
                PageId::new(u32::from_be_bytes(
                    buffer[offset..offset + 4].try_into().unwrap()
                )),
                PageId::new(i - 89)
            );
        }
    }

    #[test]
    fn test_delete_page_usable_size() {
        let pager = create_empty_pager(&[0; 512], 512, 510);
        for i in 2..=300 {
            let (page_id, _) = pager.allocate_page().unwrap();
            assert_eq!(page_id.get(), i);
        }
        assert_eq!(pager.num_pages(), 300);
        pager.commit().unwrap();

        for i in 100..230 {
            pager.delete_page(PageId::new(i).unwrap()).unwrap();
        }
        pager.commit().unwrap();
        assert_eq!(pager.num_pages(), 300);

        let page1 = pager.get_page(PAGE_ID_1).unwrap();
        let buffer = page1.buffer();
        let header = DatabaseHeader::from((&buffer[..DATABASE_HEADER_SIZE]).try_into().unwrap());
        let first_page_id = header.first_freelist_trunk_page_id().unwrap();
        assert_eq!(first_page_id, PageId::new(220).unwrap());
        assert_eq!(header.n_freelist_pages(), 130);
        drop(buffer);
        let page = pager.get_page(first_page_id).unwrap();
        let buffer = page.buffer();
        let next_page_id = PageId::new(u32::from_be_bytes(buffer[0..4].try_into().unwrap()));
        assert_eq!(next_page_id, PageId::new(100));
        let n_free_pages = u32::from_be_bytes(buffer[4..8].try_into().unwrap());
        assert_eq!(n_free_pages, 9);
        for i in 0..n_free_pages {
            let offset = (i * 4) as usize + 8;
            assert_eq!(
                PageId::new(u32::from_be_bytes(
                    buffer[offset..offset + 4].try_into().unwrap()
                )),
                PageId::new(221 + i)
            );
        }
        let page = pager.get_page(next_page_id.unwrap()).unwrap();
        let buffer = page.buffer();
        let next_page_id = PageId::new(u32::from_be_bytes(buffer[0..4].try_into().unwrap()));
        assert_eq!(next_page_id, None);
        let n_free_pages = u32::from_be_bytes(buffer[4..8].try_into().unwrap());
        assert_eq!(n_free_pages, 119);
        for i in 0..n_free_pages {
            let offset = (i * 4) as usize + 8;
            // 101 ~ 199
            assert_eq!(
                PageId::new(u32::from_be_bytes(
                    buffer[offset..offset + 4].try_into().unwrap()
                )),
                PageId::new(101 + i)
            );
        }
    }

    #[test]
    fn test_delete_page_allocate_page() {
        let pager = create_empty_pager(&[0; 512], 512, 510);
        for i in 2..=300 {
            let (page_id, _) = pager.allocate_page().unwrap();
            assert_eq!(page_id.get(), i);
        }
        assert_eq!(pager.num_pages(), 300);
        for i in 10..=200 {
            pager.delete_page(PageId::new(i).unwrap()).unwrap();
        }
        assert_eq!(pager.num_pages(), 300);
        for i in 0..=190 {
            let (page_id, _) = pager.allocate_page().unwrap();
            assert_eq!(page_id.get(), 200 - i);
        }
        assert_eq!(pager.num_pages(), 300);
        let (page_id, _) = pager.allocate_page().unwrap();
        assert_eq!(page_id.get(), 301);
        assert_eq!(pager.num_pages(), 301);
    }
}
