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

use rusqlite::Connection;
use tempfile::NamedTempFile;

use crate::pager::Pager;
use crate::DatabaseHeader;
use crate::DATABASE_HEADER_SIZE;

pub fn create_sqlite_database(queries: &[&str]) -> NamedTempFile {
    let file = NamedTempFile::new().unwrap();
    let conn = Connection::open(file.path()).unwrap();
    for query in queries {
        conn.execute(query, []).unwrap();
    }
    conn.close().unwrap();
    file
}

pub fn create_pager(file: File) -> anyhow::Result<Pager> {
    let mut header_buf = [0_u8; DATABASE_HEADER_SIZE];
    file.read_exact_at(&mut header_buf, 0)?;
    let header = DatabaseHeader::from(&header_buf);
    Pager::new(file, header.pagesize() as usize)
}

pub fn load_usable_size(file: &File) -> anyhow::Result<u32> {
    let mut header_buf = [0_u8; DATABASE_HEADER_SIZE];
    file.read_exact_at(&mut header_buf, 0)?;
    let header = DatabaseHeader::from(&header_buf);
    Ok(header.usable_size())
}

pub fn buffer_to_hex(buf: &[u8]) -> String {
    buf.iter().map(|v| format!("{v:02X}")).collect::<String>()
}
