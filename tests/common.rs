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

use prsqlite::Connection;
use prsqlite::Value;
use tempfile::NamedTempFile;

#[allow(dead_code)]
pub fn create_sqlite_database(queries: &[&str]) -> NamedTempFile {
    let file = NamedTempFile::new().unwrap();
    let conn = rusqlite::Connection::open(file.path()).unwrap();
    for query in queries {
        conn.execute(query, []).unwrap();
    }
    conn.close().unwrap();
    file
}

#[allow(dead_code)]
pub fn load_rowids(conn: &mut Connection, query: &str) -> Vec<i64> {
    let mut stmt = conn.prepare(query).unwrap();
    let mut rows = stmt.query().unwrap();
    let mut results = Vec::new();
    while let Some(row) = rows.next_row().unwrap() {
        let columns = row.parse().unwrap();
        assert_eq!(columns.len(), 1);
        assert!(matches!(columns.get(0), &Value::Integer(_)));
        let Value::Integer(rowid) = columns.get(0) else {
            unreachable!()
        };
        results.push(*rowid);
    }
    results
}

#[allow(dead_code)]
pub fn load_test_rowids(conn: &rusqlite::Connection, query: &str) -> Vec<i64> {
    let mut stmt = conn.prepare(query).unwrap();
    let mut rows = stmt.query([]).unwrap();
    let mut results = Vec::new();
    while let Some(row) = rows.next().unwrap() {
        results.push(row.get::<_, i64>(0).unwrap());
    }
    results
}

#[allow(dead_code)]
pub fn assert_same_results(
    expected: &[&[Value]],
    query: &str,
    test_conn: &rusqlite::Connection,
    conn: &mut Connection,
) {
    let mut stmt = test_conn.prepare(query).unwrap();
    let mut rows = stmt.query([]).unwrap();
    for (i, e) in expected.iter().enumerate() {
        let row = rows.next().unwrap().unwrap();
        for (j, e) in e.iter().enumerate() {
            let v = match row.get::<_, rusqlite::types::Value>(j).unwrap() {
                rusqlite::types::Value::Null => Value::Null,
                rusqlite::types::Value::Integer(v) => Value::Integer(v),
                rusqlite::types::Value::Real(v) => Value::Real(v),
                rusqlite::types::Value::Text(v) => Value::Text(v.into_bytes().into()),
                rusqlite::types::Value::Blob(v) => Value::Blob(v.into()),
            };
            assert_eq!(&v, e, "i: {}, j: {}, query: {}", i, j, query);
        }
    }

    let mut stmt = conn.prepare(query).unwrap();
    let mut rows = stmt.query().unwrap();
    for (i, e) in expected.iter().enumerate() {
        let row = rows.next_row().unwrap().unwrap();
        let columns = row.parse().unwrap();
        for (j, e) in e.iter().enumerate() {
            assert_eq!(columns.get(j), e, "i: {}, j: {}, query: {}", i, j, query);
        }
    }
}
