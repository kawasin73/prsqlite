use std::fs::File;
use std::os::unix::fs::FileExt;

use anyhow::bail;

pub type PageId = u32;
// The size of a page is more than 1024.
pub type PageBuffer = [u8];

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

    pub fn get_page(&self, id: PageId) -> anyhow::Result<&PageBuffer> {
        if id == 0 {
            bail!("page id starts from 1");
        } else if id > self.n_pages {
            bail!("page id exceeds file size");
        }
        let offset = (id - 1) as usize * self.pagesize;
        Ok(&self.buffer[offset..offset + self.pagesize])
    }
}
