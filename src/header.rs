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

use crate::pager::PageId;
use crate::pager::MAX_PAGE_SIZE;

const MAGIC_HEADER: &[u8; 16] = b"SQLite format 3\0";
pub const DATABASE_HEADER_SIZE: usize = 100;
pub struct DatabaseHeader<'a>(&'a [u8; DATABASE_HEADER_SIZE]);

impl<'a> DatabaseHeader<'a> {
    pub fn from(buf: &'a [u8; DATABASE_HEADER_SIZE]) -> Self {
        Self(buf)
    }

    pub fn validate(&self) -> std::result::Result<(), &'static str> {
        if !self.validate_magic_header() {
            return Err("Invalid magic header");
        }
        if !self.validate_pagesize() {
            return Err("Invalid pagesize");
        }
        Ok(())
    }

    fn validate_magic_header(&self) -> bool {
        let magic_header: &[u8; 16] = self.0[0..16].try_into().unwrap();
        magic_header == MAGIC_HEADER
    }

    fn validate_pagesize(&self) -> bool {
        let pagesize = self.pagesize();
        (512..=MAX_PAGE_SIZE as u32).contains(&pagesize) && (pagesize - 1) & pagesize == 0
    }

    pub fn pagesize(&self) -> u32 {
        // If the original big endian value is 1, it means 65536.
        (self.0[16] as u32) << 8 | (self.0[17] as u32) << 16
    }

    pub fn reserved(&self) -> u8 {
        self.0[20]
    }

    pub fn n_pages(&self) -> u32 {
        u32::from_be_bytes(self.0[28..32].try_into().unwrap())
    }

    pub fn first_freelist_trunk_page_id(&self) -> Option<PageId> {
        PageId::new(u32::from_be_bytes(self.0[32..36].try_into().unwrap()))
    }

    pub fn n_freelist_pages(&self) -> u32 {
        u32::from_be_bytes(self.0[36..40].try_into().unwrap())
    }
}

pub struct DatabaseHeaderMut<'a>(&'a mut [u8; DATABASE_HEADER_SIZE]);

impl<'a> DatabaseHeaderMut<'a> {
    pub fn from(buf: &'a mut [u8; DATABASE_HEADER_SIZE]) -> Self {
        Self(buf)
    }

    pub fn set_n_pages(&mut self, n_pages: u32) {
        self.0[28..32].copy_from_slice(&n_pages.to_be_bytes());
    }

    pub fn set_first_freelist_trunk_page_id(&mut self, page_id: Option<PageId>) {
        let page_id = page_id.map(|id| id.get()).unwrap_or(0);
        self.0[32..36].copy_from_slice(&page_id.to_be_bytes());
    }

    pub fn set_first_freelist_trunk_page_id_raw(&mut self, page_id: &[u8; 4]) {
        self.0[32..36].copy_from_slice(page_id);
    }

    pub fn set_n_freelist_pages(&mut self, pages: u32) {
        self.0[36..40].copy_from_slice(&pages.to_be_bytes());
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;
    use crate::test_utils::*;

    #[test]
    fn pagesize() {
        for shift in 9..16 {
            // 512 ~ 32768
            let size: u16 = 1 << shift;
            let bytes = size.to_be_bytes();
            let mut buf = [0_u8; DATABASE_HEADER_SIZE];
            buf[16] = bytes[0];
            buf[17] = bytes[1];
            let header = DatabaseHeader::from(&buf);

            assert_eq!(header.pagesize(), size as u32);
        }

        // the pagesize "1" means 65536
        let bytes = 1_u16.to_be_bytes();
        let mut buf = [0_u8; DATABASE_HEADER_SIZE];
        buf[16] = bytes[0];
        buf[17] = bytes[1];
        let header = DatabaseHeader::from(&buf);

        assert_eq!(header.pagesize(), 65536);
    }

    #[test]
    fn n_pages() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let buf = fs::read(file.path()).unwrap();

        let header = DatabaseHeader::from(buf[0..DATABASE_HEADER_SIZE].try_into().unwrap());

        assert_eq!(header.n_pages(), 2);
    }

    #[test]
    fn set_n_pages() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let mut buf = fs::read(file.path()).unwrap();
        let mut_buf = &mut buf[0..DATABASE_HEADER_SIZE];

        let mut header = DatabaseHeaderMut::from(mut_buf.try_into().unwrap());

        header.set_n_pages(3);

        let header = DatabaseHeader::from(buf[0..DATABASE_HEADER_SIZE].try_into().unwrap());
        assert_eq!(header.n_pages(), 3);
    }

    #[test]
    fn validate_database_header() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let buf = fs::read(file.path()).unwrap();

        let header = DatabaseHeader::from(buf[0..DATABASE_HEADER_SIZE].try_into().unwrap());

        assert!(header.validate_magic_header());
        assert_eq!(header.pagesize(), 4096);
        assert!(header.validate_pagesize());
    }
}
