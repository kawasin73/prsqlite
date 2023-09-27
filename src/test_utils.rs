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

use std::fmt::Write;
use std::fs::File;
use std::os::unix::fs::FileExt;
use std::path::Path;

use tempfile::NamedTempFile;

use crate::btree::BtreeContext;
use crate::pager::PageId;
use crate::pager::Pager;
use crate::schema::Schema;
use crate::Connection;
use crate::DatabaseHeader;
use crate::Expression;
use crate::SelectStatement;
use crate::DATABASE_HEADER_SIZE;

pub fn create_sqlite_database(queries: &[&str]) -> NamedTempFile {
    let file = NamedTempFile::new().unwrap();
    let conn = rusqlite::Connection::open(file.path()).unwrap();
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

pub fn create_empty_pager(file_content: &[u8], pagesize: usize) -> Pager {
    let file = NamedTempFile::new().unwrap();
    file.as_file().write_all_at(file_content, 0).unwrap();
    Pager::new(file.as_file().try_clone().unwrap(), pagesize).unwrap()
}

pub fn load_btree_context(file: &File) -> anyhow::Result<BtreeContext> {
    let mut header_buf = [0_u8; DATABASE_HEADER_SIZE];
    file.read_exact_at(&mut header_buf, 0)?;
    let header = DatabaseHeader::from(&header_buf);
    Ok(BtreeContext::new(header.usable_size()))
}

pub fn buffer_to_hex(buf: &[u8]) -> String {
    buf.iter().fold(String::new(), |mut output, v| {
        let _ = write!(output, "{v:02X}");
        output
    })
}

pub fn find_table_page_id(table: &str, filepath: &Path) -> PageId {
    let mut conn = Connection::open(filepath).unwrap();
    let schema_table = Schema::schema_table();
    let columns = schema_table
        .get_all_columns()
        .map(Expression::Column)
        .collect::<Vec<_>>();
    let schema = Schema::generate(
        SelectStatement::new(&mut conn, schema_table.root_page_id, columns, None),
        schema_table,
    )
    .unwrap();
    schema.get_table(table.as_bytes()).unwrap().root_page_id
}

pub fn find_index_page_id(index: &str, filepath: &Path) -> PageId {
    let mut conn = Connection::open(filepath).unwrap();
    let schema_table = Schema::schema_table();
    let columns = schema_table
        .get_all_columns()
        .map(Expression::Column)
        .collect::<Vec<_>>();
    let schema = Schema::generate(
        SelectStatement::new(&mut conn, schema_table.root_page_id, columns, None),
        schema_table,
    )
    .unwrap();
    schema.get_index(index.as_bytes()).unwrap().root_page_id
}
