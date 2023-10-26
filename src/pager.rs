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

use std::cell::Cell;
use std::cell::Ref;
use std::cell::RefCell;
use std::cell::RefMut;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fs::File;
use std::ops::Deref;
use std::ops::DerefMut;
use std::os::unix::fs::FileExt;
use std::rc::Rc;

use anyhow::bail;

use crate::DATABASE_HEADER_SIZE;

pub const MAX_PAGE_SIZE: usize = 65536;

pub type PageId = u32;

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

// The size of a page is more than 512.
pub struct PageBuffer<'a>(Ref<'a, RawPage>);

impl<'a> Deref for PageBuffer<'a> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.0.buf
    }
}
pub struct PageBufferMut<'a>(RefMut<'a, RawPage>);

impl PageBufferMut<'_> {
    pub fn swap(&mut self, buffer: &mut TemporaryPage) {
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

pub const ROOT_PAGE_ID: PageId = 1;

pub struct Pager {
    file: File,
    n_pages: Cell<u32>,
    n_pages_stable: Cell<u32>,
    cache: PageCache,
}

impl Pager {
    pub fn new(file: File, n_pages: u32, pagesize: u32) -> anyhow::Result<Self> {
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

    pub fn allocate_page(&self) -> anyhow::Result<(PageId, MemPage)> {
        // TODO: Use a page from free list.

        let page_id = self.n_pages.get() + 1;
        self.n_pages.set(page_id);
        let (page, is_new) = self.cache.get_page(page_id);
        assert!(is_new);
        page.borrow_mut().is_dirty = true;
        // TODO: setup journal

        let header_offset = if page_id == 1 {
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

    pub fn get_page(&self, id: PageId) -> anyhow::Result<MemPage> {
        match id {
            0 => bail!("page id starts from 1"),
            id if id > self.n_pages.get() => bail!("page id exceeds file size"),
            id => {
                let (page, is_new) = self.cache.get_page(id);
                if is_new {
                    let mut raw_page = page.borrow_mut();
                    self.file
                        .read_exact_at(&mut raw_page.buf, self.page_offset(id))?;
                }
                let header_offset = if id == 1 { DATABASE_HEADER_SIZE } else { 0 };
                Ok(MemPage {
                    page,
                    header_offset,
                })
            }
        }
    }

    pub fn make_page_mut<'a>(&self, page: &'a MemPage) -> anyhow::Result<PageBufferMut<'a>> {
        let mut raw_page = page
            .page
            .try_borrow_mut()
            .map_err(|e| anyhow::anyhow!("buffer mut: {}", e))?;

        if !raw_page.is_dirty {
            raw_page.is_dirty = true;
            // TODO: setup journal
        }

        Ok(PageBufferMut(raw_page))
    }

    pub fn commit(&self) -> anyhow::Result<()> {
        for (page_id, page) in self.cache.map.borrow().iter() {
            let raw_page = page.borrow();
            if raw_page.is_dirty {
                self.file
                    .write_all_at(&raw_page.buf, self.page_offset(*page_id))?;
                drop(raw_page);
                // TODO: How to guarantee page is not referenced?
                page.borrow_mut().is_dirty = false;
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
        (page_id - 1) as u64 * self.cache.pagesize as u64
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
