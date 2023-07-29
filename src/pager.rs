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

use std::cell::Ref;
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fs::File;
use std::os::unix::fs::FileExt;
use std::rc::Rc;

use anyhow::bail;

use crate::DATABASE_HEADER_SIZE;

pub type PageId = u32;
// The size of a page is more than 512.
pub type PageBuffer<'a> = Ref<'a, Vec<u8>>;

pub const ROOT_PAGE_ID: PageId = 1;

pub struct Pager {
    file: File,
    n_pages: u32,
    cache: PageCache,
}

impl Pager {
    pub fn new(file: File, pagesize: usize) -> anyhow::Result<Self> {
        let file_len = file.metadata()?.len();
        assert!(file_len % pagesize as u64 == 0);
        let n_pages = file_len / (pagesize as u64);
        Ok(Self {
            file,
            cache: PageCache::new(pagesize),
            n_pages: n_pages.try_into()?,
        })
    }

    pub fn get_page(&self, id: PageId) -> anyhow::Result<MemPage> {
        match id {
            0 => bail!("page id starts from 1"),
            id if id > self.n_pages => bail!("page id exceeds file size"),
            id => {
                let (page, is_new) = self.cache.get_page(id);
                if is_new {
                    let mut buffer = page.borrow_mut();
                    let offset = (id - 1) as usize * buffer.len();
                    self.file.read_exact_at(&mut buffer, offset as u64)?;
                }
                let header_offset = if id == 1 { DATABASE_HEADER_SIZE } else { 0 };
                Ok(MemPage {
                    page,
                    header_offset,
                })
            }
        }
    }
}

pub struct MemPage {
    page: Rc<RefCell<Vec<u8>>>,
    pub header_offset: usize,
}

impl MemPage {
    pub fn buffer(&self) -> PageBuffer {
        self.page.borrow()
    }
}

struct PageCache {
    map: RefCell<HashMap<PageId, Rc<RefCell<Vec<u8>>>>>,
    pagesize: usize,
}

impl PageCache {
    fn new(pagesize: usize) -> Self {
        Self {
            map: RefCell::new(HashMap::new()),
            pagesize,
        }
    }

    fn get_page(&self, id: PageId) -> (Rc<RefCell<Vec<u8>>>, bool) {
        match self.map.borrow_mut().entry(id) {
            Entry::Occupied(entry) => (entry.get().clone(), false),
            Entry::Vacant(entry) => {
                let page = Rc::new(RefCell::new(vec![0_u8; self.pagesize]));
                entry.insert(page.clone());
                (page, true)
            }
        }
    }
}
