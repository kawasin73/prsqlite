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
pub fn load_rowids(conn: &Connection, query: &str) -> Vec<i64> {
    let stmt = conn.prepare(query).unwrap();
    let mut rows = stmt.query().unwrap();
    let mut results = Vec::new();
    while let Some(row) = rows.next_row().unwrap() {
        let columns = row.parse().unwrap();
        assert_eq!(columns.len(), 1);
        assert!(matches!(columns.get(0), Some(&Value::Integer(_))));
        let Some(Value::Integer(rowid)) = columns.get(0) else {
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

#[macro_export]
macro_rules! assert_same_result_prsqlite {
    ($rows:ident, $result:expr, $msg:expr) => {
        let row = $rows.next_row().unwrap().unwrap();
        let columns = row.parse().unwrap();
        for (idx, e) in $result.iter().enumerate() {
            assert_eq!(&columns.get(idx), e, "idx: {}, {}", idx, $msg);
        }
        drop(row);
    };
}

#[allow(dead_code)]
pub fn assert_same_results(
    expected: &[&[Option<&Value>]],
    query: &str,
    test_conn: &rusqlite::Connection,
    conn: &Connection,
) {
    let mut stmt = test_conn.prepare(query).unwrap();
    let mut rows = stmt.query([]).unwrap();
    for (i, e) in expected.iter().enumerate() {
        let row = rows.next().unwrap().unwrap();
        for (j, e) in e.iter().enumerate() {
            let v = match row.get::<_, rusqlite::types::Value>(j).unwrap() {
                rusqlite::types::Value::Null => {
                    assert!(e.is_none(), "i: {}, j: {}, query: {}", i, j, query);
                    continue;
                }
                rusqlite::types::Value::Integer(v) => Value::Integer(v),
                rusqlite::types::Value::Real(v) => Value::Real(v),
                rusqlite::types::Value::Text(v) => Value::Text(v.into_bytes().into()),
                rusqlite::types::Value::Blob(v) => Value::Blob(v.into()),
            };
            assert_eq!(&Some(&v), e, "i: {}, j: {}, query: {}", i, j, query);
        }
    }
    assert!(rows.next().unwrap().is_none());

    let stmt = conn.prepare(query).unwrap();
    let mut rows = stmt.query().unwrap();
    for (i, e) in expected.iter().enumerate() {
        assert_same_result_prsqlite!(rows, e, format!("i: {i}, query: {query}"));
    }
    assert!(rows.next_row().unwrap().is_none());
}
