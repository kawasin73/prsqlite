use std::ptr::copy_nonoverlapping;

use anyhow::bail;

use crate::btree::BtreeInteriorTableCell;
use crate::btree::BtreeLeafTableCell;
use crate::btree::BtreePageHeader;
use crate::btree::OverflowPage;
use crate::pager::MemPage;
use crate::pager::PageId;
use crate::pager::Pager;

pub struct BtreePayload<'a> {
    pager: &'a Pager,
    size: i64,
    local_payload: &'a [u8],
    overflow: Option<OverflowPage>,
}

impl<'a> BtreePayload<'a> {
    fn new(
        pager: &'a Pager,
        usable_size: u32,
        cell: BtreeLeafTableCell<'a>,
    ) -> anyhow::Result<Self> {
        let (_, size, local_payload, overflow) = cell
            .parse(usable_size)
            .map_err(|e| anyhow::anyhow!("parse tree leaf table cell: {:?}", e))?;
        Ok(Self {
            pager,
            size,
            local_payload,
            overflow,
        })
    }

    /// The size of the payload.
    pub fn size(&self) -> i64 {
        self.size
    }

    /// The local payload.
    ///
    /// This may not be the entire payload if there is overflow page.
    pub fn buf(&self) -> &'a [u8] {
        self.local_payload
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
    pub unsafe fn load(&self, offset: i64, buf: &mut [u8]) -> anyhow::Result<usize> {
        if offset >= self.size {
            bail!("offset exceeds payload size");
        }
        let mut n_loaded = 0;
        let mut offset = offset;
        let mut buf = buf;
        let mut cur = 0;
        let mut payload = self.local_payload;
        let mut overflow = self.overflow;
        loop {
            if offset < cur + payload.len() as i64 {
                let local_offset = (offset - cur) as usize;
                let n = std::cmp::min(payload.len() - local_offset, buf.len());

                // SAFETY: n is less than buf.len() and payload.len().
                // SAFETY: payload and buf do not overlap.
                unsafe {
                    copy_nonoverlapping(payload[local_offset..].as_ptr(), buf.as_mut_ptr(), n);
                }
                n_loaded += n;
                offset += n as i64;
                buf = &mut buf[n..];
            }
            cur += payload.len() as i64;
            if buf.len() == 0 || cur >= self.size {
                break;
            }

            let overflow_page = match overflow {
                Some(overflow) => overflow,
                None => bail!("overflow page is not found"),
            };
            let page = self.pager.get_page(overflow_page.page_id())?;
            (payload, overflow) = overflow_page
                .parse(&page)
                .map_err(|e| anyhow::anyhow!("parse overflow: {:?}", e))?;
        }

        Ok(n_loaded)
    }
}

pub struct BtreeCursor<'a> {
    pager: &'a Pager,
    usable_size: u32,
    current_page_id: PageId,
    current_page: MemPage<'a>,
    idx_cell: u16,
    parent_pages: Vec<(PageId, u16)>,
    pub last_error: Option<anyhow::Error>,
}

impl<'a> BtreeCursor<'a> {
    pub fn new(root_page: PageId, pager: &'a Pager, usable_size: u32) -> Self {
        Self {
            pager,
            usable_size,
            current_page_id: root_page,
            current_page: pager.get_page(root_page).unwrap(),
            idx_cell: 0,
            parent_pages: Vec::new(),
            last_error: None,
        }
    }
}

impl<'a> Iterator for BtreeCursor<'a> {
    type Item = BtreePayload<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.current_page = match self.pager.get_page(self.current_page_id) {
            Ok(page) => page,
            Err(e) => {
                self.last_error = Some(e);
                return None;
            }
        };
        let page_header = BtreePageHeader::from_page(&self.current_page);
        if !page_header.is_leaf() && self.idx_cell == page_header.n_cells() {
            self.idx_cell += 1;
            self.parent_pages
                .push((self.current_page_id, self.idx_cell));
            self.current_page_id = page_header.right_page_id();
            self.idx_cell = 0;
            self.next()
        } else if self.idx_cell >= page_header.n_cells() {
            let (page_id, idx_cell) = match self.parent_pages.pop() {
                Some((page_id, idx_cell)) => (page_id, idx_cell),
                None => {
                    return None;
                }
            };
            self.current_page_id = page_id;
            self.idx_cell = idx_cell + 1;
            self.next()
        } else {
            if page_header.is_leaf() {
                let cell = match BtreeLeafTableCell::get(&self.current_page, self.idx_cell) {
                    Ok(cell) => cell,
                    Err(e) => {
                        self.last_error =
                            Some(anyhow::anyhow!("get btree leaf table cell: {:?}", e));
                        return None;
                    }
                };
                let payload = match BtreePayload::new(self.pager, self.usable_size, cell) {
                    Ok(payload) => payload,
                    Err(e) => {
                        self.last_error = Some(e);
                        return None;
                    }
                };
                self.idx_cell += 1;
                Some(payload)
            } else {
                let cell = match BtreeInteriorTableCell::get(&self.current_page, self.idx_cell) {
                    Ok(cell) => cell,
                    Err(e) => {
                        self.last_error =
                            Some(anyhow::anyhow!("get btree interior table cell: {:?}", e));
                        return None;
                    }
                };
                let page_id = cell.page_id();
                self.parent_pages
                    .push((self.current_page_id, self.idx_cell));
                self.current_page_id = page_id;
                self.idx_cell = 0;
                self.next()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::find_table_page_id;
    use crate::parse_records;
    use crate::test_utils::*;
    use crate::Record;

    #[test]
    fn test_btree_cursor_single_page() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "INSERT INTO example(col) VALUES (0);",
            "INSERT INTO example(col) VALUES (1);",
            "INSERT INTO example(col) VALUES (2);",
        ]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let usable_size = load_usable_size(file.as_file()).unwrap();
        let page_id = find_table_page_id(b"example", 1, &pager, usable_size).unwrap();

        let mut cursor = BtreeCursor::new(page_id, &pager, usable_size);

        let payload = cursor.next();
        assert!(payload.is_some());
        let mut records = vec![Record::Null];
        let size = parse_records(payload.unwrap().buf(), &mut records).unwrap();
        assert_eq!(size, 1);
        assert_eq!(records[0].to_i64().unwrap(), 0);

        let payload = cursor.next();
        assert!(payload.is_some());
        let mut records = vec![Record::Null];
        let size = parse_records(payload.unwrap().buf(), &mut records).unwrap();
        assert_eq!(size, 1);
        assert_eq!(records[0].to_i64().unwrap(), 1);

        let payload = cursor.next();
        assert!(payload.is_some());
        let mut records = vec![Record::Null];
        let size = parse_records(payload.unwrap().buf(), &mut records).unwrap();
        assert_eq!(size, 1);
        assert_eq!(records[0].to_i64().unwrap(), 2);

        assert!(cursor.next().is_none());
    }

    #[test]
    fn test_btree_cursor_empty_records() {
        let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let usable_size = load_usable_size(file.as_file()).unwrap();
        let page_id = find_table_page_id(b"example", 1, &pager, usable_size).unwrap();

        let mut cursor = BtreeCursor::new(page_id, &pager, usable_size);
        assert!(cursor.next().is_none());
    }

    #[test]
    fn test_btree_cursor_multiple_page() {
        let buf = vec![0; 4000];
        let mut inserts = Vec::new();
        // 1000 byte blob entry occupies 1 page. These 2000 entries introduce
        // 2 level interior pages and 1 leaf page level.
        for i in 0..1000 {
            inserts.push(format!(
                "INSERT INTO example(col,buf) VALUES ({},X'{}');",
                i,
                buffer_to_hex(&buf)
            ));
        }
        for i in 0..1000 {
            inserts.push(format!("INSERT INTO example(col) VALUES ({});", i));
        }
        let mut queries = vec!["CREATE TABLE example(col,buf);"];
        queries.extend(inserts.iter().map(|s| s.as_str()));
        let file = create_sqlite_database(&queries);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let usable_size = load_usable_size(file.as_file()).unwrap();
        let page_id = find_table_page_id(b"example", 1, &pager, usable_size).unwrap();

        let mut cursor = BtreeCursor::new(page_id, &pager, usable_size);

        for i in 0..1000 {
            let payload = cursor.next();
            assert!(payload.is_some());
            let mut records = vec![Record::Null, Record::Null];
            let size = parse_records(payload.unwrap().buf(), &mut records).unwrap();
            assert_eq!(size, 2);
            assert_eq!(records[0].to_i64().unwrap(), i);
            assert_eq!(records[1].to_slice().unwrap().len(), 4000);
        }
        for i in 0..1000 {
            let payload = cursor.next();
            assert!(payload.is_some());
            let mut records = vec![Record::Null, Record::Null];
            let size = parse_records(payload.unwrap().buf(), &mut records).unwrap();
            assert_eq!(size, 2);
            assert_eq!(records[0].to_i64().unwrap(), i);
            assert!(records[1].is_null());
        }

        assert!(cursor.next().is_none());
    }

    #[test]
    fn test_overflow_payload() {
        let mut queries = vec!["CREATE TABLE example(col);"];
        let mut buf = Vec::with_capacity(10000);
        for i in 0..10000 {
            buf.push((i % 256) as u8);
        }
        let query = format!(
            "INSERT INTO example(col) VALUES (X'{}');",
            buffer_to_hex(&buf)
        );
        queries.push(&query);
        let file = create_sqlite_database(&queries);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let usable_size = load_usable_size(file.as_file()).unwrap();
        let page_id = find_table_page_id(b"example", 1, &pager, usable_size).unwrap();

        let mut cursor = BtreeCursor::new(page_id, &pager, usable_size);

        let payload = cursor.next();
        assert!(payload.is_some());
        let payload = payload.unwrap();

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
}
