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

use prsqlite::{Connection, Record};
use tempfile::NamedTempFile;

fn create_sqlite_database(queries: &[&str]) -> NamedTempFile {
    let file = NamedTempFile::new().unwrap();
    let conn = rusqlite::Connection::open(file.path()).unwrap();
    for query in queries {
        conn.execute(&query, []).unwrap();
    }
    conn.close().unwrap();
    file
}

#[test]
fn test_select_all_from_table() {
    let mut queries = vec![
        "CREATE TABLE example(col);",
        "CREATE TABLE example2(col1, col2);",
        "CREATE TABLE example3(col1, col2, col3);",
        "INSERT INTO example3(col1, col2, col3) VALUES (null, true, false);",
        "INSERT INTO example3(col1, col3) VALUES (10000, \"hello\");",
    ];
    let blob_query = format!(
        "INSERT INTO example3(col1, col2) VALUES (X'{}', 20000);",
        "FF".repeat(10000)
    );
    queries.push(&blob_query);
    let file = create_sqlite_database(&queries);

    let conn = Connection::open(file.path()).unwrap();
    let mut stmt = conn.prepare("SELECT * FROM example3;").unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next().unwrap().unwrap();
    assert!(matches!(row.get(0), Record::Null));
    assert!(matches!(row.get(1), Record::One));
    assert!(matches!(row.get(2), Record::Zero));
    assert!(matches!(row.get(3), Record::Null));

    let row = rows.next().unwrap().unwrap();
    assert_eq!(row.get(0).to_i64().unwrap(), 10000);
    assert!(matches!(row.get(1), Record::Null));
    assert!(matches!(row.get(2), Record::Text(b"hello")));
    assert!(matches!(row.get(3), Record::Null));

    let row = rows.next().unwrap().unwrap();
    assert!(matches!(row.get(0), Record::Blob(_)));
    assert_eq!(row.get(0).to_slice().unwrap(), &[0xFF; 10000]);
    assert_eq!(row.get(1).to_i64().unwrap(), 20000);
    assert!(matches!(row.get(2), Record::Null));
    assert!(matches!(row.get(3), Record::Null));

    assert!(rows.next().unwrap().is_none());
}
