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

use std::fs::File;
use std::os::unix::fs::FileExt;

use anyhow::bail;

use crate::DATABASE_HEADER_SIZE;

pub type PageId = u32;

pub const ROOT_PAGE_ID: PageId = 1;

pub struct Pager {
    n_pages: u32,
    pagesize: usize,
    buffer: Vec<u8>,
}

impl Pager {
    pub fn new(file: File, pagesize: usize) -> anyhow::Result<Self> {
        let file_len = file.metadata()?.len();
        assert!(file_len % pagesize as u64 == 0);
        let n_pages = file_len / (pagesize as u64);
        let mut buffer = Vec::with_capacity(file_len as usize);
        // SAFETY: buf is allocated with the same size as file.
        unsafe {
            buffer.set_len(file_len as usize);
        }
        file.read_exact_at(&mut buffer, 0)?;
        Ok(Self {
            pagesize,
            n_pages: n_pages.try_into()?,
            buffer,
        })
    }

    pub fn get_page<'a>(&'a self, id: PageId) -> anyhow::Result<MemPage<'a>> {
        match id {
            0 => bail!("page id starts from 1"),
            1 => Ok(MemPage {
                buffer: &self.buffer[..self.pagesize],
                header_offset: DATABASE_HEADER_SIZE,
            }),
            _ if id > self.n_pages => bail!("page id exceeds file size"),
            _ => {
                let offset = (id - 1) as usize * self.pagesize;
                Ok(MemPage {
                    buffer: &self.buffer[offset..offset + self.pagesize],
                    header_offset: 0,
                })
            }
        }
    }
}

pub struct MemPage<'a> {
    // The size of a page is more than 512.
    pub buffer: &'a [u8],
    pub header_offset: usize,
}
