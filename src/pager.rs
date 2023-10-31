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

use crate::header::DATABASE_HEADER_SIZE;

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
    n_pages: Cell<u32>,
    n_pages_stable: Cell<u32>,
    cache: PageCache,
}

impl Pager {
    pub fn new(file: File, n_pages: u32, pagesize: u32) -> Result<Self> {
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
        })
    }

    pub fn allocate_page(&self) -> Result<(PageId, MemPage)> {
        // TODO: Use a page from free list.

        let page_id = self.n_pages.get() + 1;
        if page_id > MAX_PAGE_ID {
            return Err(Error::NoSpace);
        }
        self.n_pages.set(page_id);
        let page_id = PageId::new(page_id).unwrap();
        let (page, is_new) = self.cache.get_page(page_id);
        assert!(is_new);
        page.borrow_mut().is_dirty = true;
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

        // TODO: rollback journal
    }

    pub fn is_file_size_changed(&self) -> bool {
        self.n_pages.get() != self.n_pages_stable.get()
    }

    pub fn num_pages(&self) -> u32 {
        self.n_pages.get()
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
    pub fn buffer(&self) -> PageBuffer {
        PageBuffer(self.page.borrow())
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let file = tempfile::tempfile().unwrap();
        file.write_all_at(&[0_u8; 4096], 0).unwrap();
        let pager = Pager::new(file, 1, 4096).unwrap();
        assert_eq!(pager.num_pages(), 1);

        let file = tempfile::tempfile().unwrap();
        file.write_all_at(&[0_u8; 4096 * 2], 0).unwrap();
        let pager = Pager::new(file, 2, 4096).unwrap();
        assert_eq!(pager.num_pages(), 2);

        let file = tempfile::tempfile().unwrap();
        assert!(matches!(
            Pager::new(file, u32::MAX, 4096).err().unwrap(),
            Error::InvalidFile
        ));
    }

    #[test]
    fn test_get_page() {
        let file = tempfile::tempfile().unwrap();
        file.write_all_at(&[1_u8; 4096], 0).unwrap();
        file.write_all_at(&[2_u8; 4096], 4096).unwrap();
        let pager = Pager::new(file, 2, 4096).unwrap();

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
        let pager = Pager::new(file, 2, 4096).unwrap();

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
        let pager = Pager::new(file, 1, 4096).unwrap();

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
        let pager = Pager::new(file, 2, 4096).unwrap();
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
        let pager = Pager::new(file.reopen().unwrap(), 2, 4096).unwrap();

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
        let pager = Pager::new(file, 1, 4096).unwrap();

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
        file.as_file().write_all_at(&[1_u8; 4096], 0).unwrap();
        let pager = Pager::new(file.reopen().unwrap(), 1, 4096).unwrap();

        let page = pager.get_page(PAGE_ID_1).unwrap();
        let mut buffer = pager.make_page_mut(&page).unwrap();
        buffer.fill(3);
        drop(buffer);

        pager.abort();

        assert_eq!(
            pager.get_page(PAGE_ID_1).unwrap().buffer().deref(),
            [1_u8; 4096].as_slice()
        );
        let mut buf = [0; 4096];
        file.as_file().read_exact_at(&mut buf, 0).unwrap();
        assert_eq!(buf, [1_u8; 4096]);
    }

    #[test]
    fn test_allocate_page() {
        let file = tempfile::NamedTempFile::new().unwrap();
        let pager = Pager::new(file.reopen().unwrap(), 0, 4096).unwrap();
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
        let pager = Pager::new(file.reopen().unwrap(), 2, 4096).unwrap();

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
        let pager = Pager::new(file.reopen().unwrap(), MAX_PAGE_ID, 4096).unwrap();
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
        let pager = Pager::new(file.reopen().unwrap(), 2, 4096).unwrap();

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
}
