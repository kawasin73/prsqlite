use std::cell::Ref;
use std::cell::RefCell;
use std::fs::File;
use std::os::unix::fs::FileExt;

use anyhow::bail;

pub type PageId = u32;

pub struct Pager {
    file: File,
    n_pages: u32,
    pagesize: usize,
    cache: PageCache,
}

impl Pager {
    pub fn new(file: File, pagesize: usize, cache_size: usize) -> anyhow::Result<Self> {
        let file_len = file.metadata()?.len();
        assert!(file_len % pagesize as u64 == 0);
        let n_pages = file_len / (pagesize as u64);
        Ok(Self {
            file,
            pagesize,
            n_pages: n_pages.try_into()?,
            cache: PageCache::new(pagesize, cache_size),
        })
    }

    pub fn get_page(&self, id: PageId) -> anyhow::Result<Ref<Page>> {
        if id == 0 {
            bail!("page id starts from 1");
        } else if id > self.n_pages {
            bail!("page id exceeds file size");
        }
        if let Some(page) = self.cache.get_page(id) {
            let refpage = page.borrow();
            if refpage.initialized {
                Ok(refpage)
            } else {
                drop(refpage);
                // There must not be any reference for the page if the page is
                // not initialized.
                let mut mutpage = page.borrow_mut();
                let offset = (id - 1) as u64 * self.pagesize as u64;
                self.file.read_exact_at(&mut mutpage.buf, offset)?;
                mutpage.initialized = true;
                drop(mutpage);
                Ok(page.borrow())
            }
        } else {
            bail!("page not found");
        }
    }
}

pub struct Page {
    buf: Vec<u8>,
    initialized: bool,
}

impl Page {
    pub fn get_buf<'a>(&'a self) -> &'a [u8] {
        &self.buf
    }
}

struct PageCache {
    pages: Vec<RefCell<Page>>,
}

impl PageCache {
    fn new(pagesize: usize, size: usize) -> Self {
        let mut pages = Vec::with_capacity(size);
        for _ in 0..size {
            pages.push(RefCell::new(Page {
                // TODO: allocate big memory once and chop it into pages.
                buf: vec![0_u8; pagesize],
                initialized: false,
            }))
        }
        PageCache { pages }
    }

    fn get_page(&self, id: PageId) -> Option<&RefCell<Page>> {
        // TODO: convert page id into page using hashmap.
        let idx = (id - 1) as usize;
        self.pages.get(idx)
    }
}
