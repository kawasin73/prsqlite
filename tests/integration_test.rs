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

fn create_sqlite_database(queries: &[&str]) -> NamedTempFile {
    let file = NamedTempFile::new().unwrap();
    let conn = rusqlite::Connection::open(file.path()).unwrap();
    for query in queries {
        conn.execute(query, []).unwrap();
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

    let mut conn = Connection::open(file.path()).unwrap();
    let mut stmt = conn.prepare("SELECT * FROM example3;").unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 3);
    assert_eq!(columns.get(0), &Value::Null);
    assert_eq!(columns.get(1), &Value::Integer(1));
    assert_eq!(columns.get(2), &Value::Integer(0));
    assert_eq!(columns.get(3), &Value::Null);
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 3);
    assert_eq!(columns.get(0), &Value::Integer(10000));
    assert_eq!(columns.get(1), &Value::Null);
    assert_eq!(columns.get(2), &Value::Text(b"hello"));
    assert_eq!(columns.get(3), &Value::Null);
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 3);
    assert_eq!(columns.get(0), &Value::Blob(&[0xFF; 10000]));
    assert_eq!(columns.get(1), &Value::Integer(20000));
    assert_eq!(columns.get(2), &Value::Null);
    assert_eq!(columns.get(3), &Value::Null);
    drop(row);

    assert!(rows.next_row().unwrap().is_none());
}

#[test]
fn test_select_partial() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col1, col2, col3);",
        "INSERT INTO example(col1, col2, col3) VALUES (1, 2, 3);",
        "INSERT INTO example(col1, col2, col3) VALUES (4, 5, 6);",
        "INSERT INTO example(col1, col2, col3) VALUES (7, 8, 9);",
    ]);

    let mut conn = Connection::open(file.path()).unwrap();
    let mut stmt = conn.prepare("SELECT col3, col1 FROM example;").unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(3));
    assert_eq!(columns.get(1), &Value::Integer(1));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(6));
    assert_eq!(columns.get(1), &Value::Integer(4));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(9));
    assert_eq!(columns.get(1), &Value::Integer(7));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());
}

#[test]
fn test_select_rowid() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col);",
        "CREATE TABLE example2(col, roWid);",
        "INSERT INTO example(col) VALUES (10);",
        "INSERT INTO example(col) VALUES (20);",
        "INSERT INTO example2(col) VALUES (10);",
        "INSERT INTO example2(col, rowid) VALUES (20, 100);",
    ]);

    let mut conn = Connection::open(file.path()).unwrap();
    let mut stmt = conn.prepare("SELECT col, RoWid FROM example;").unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(10));
    assert_eq!(columns.get(1), &Value::Integer(1));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(20));
    assert_eq!(columns.get(1), &Value::Integer(2));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());

    let mut conn = Connection::open(file.path()).unwrap();
    let mut stmt = conn.prepare("SELECT col, Rowid FROM example2;").unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(10));
    assert_eq!(columns.get(1), &Value::Null);
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(20));
    assert_eq!(columns.get(1), &Value::Integer(100));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());
}

#[test]
fn test_select_column_name_and_all() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col1, col2, col3);",
        "INSERT INTO example(col1, col2, col3) VALUES (1, 2, 3);",
        "INSERT INTO example(col1, col2, col3) VALUES (4, 5, 6);",
        "INSERT INTO example(col1, col2, col3) VALUES (7, 8, 9);",
    ]);

    let mut conn = Connection::open(file.path()).unwrap();
    let mut stmt = conn
        .prepare("SELECT col3, col3, *, col1 FROM example;")
        .unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 6);
    assert_eq!(columns.get(0), &Value::Integer(3));
    assert_eq!(columns.get(1), &Value::Integer(3));
    assert_eq!(columns.get(2), &Value::Integer(1));
    assert_eq!(columns.get(3), &Value::Integer(2));
    assert_eq!(columns.get(4), &Value::Integer(3));
    assert_eq!(columns.get(5), &Value::Integer(1));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 6);
    assert_eq!(columns.get(0), &Value::Integer(6));
    assert_eq!(columns.get(1), &Value::Integer(6));
    assert_eq!(columns.get(2), &Value::Integer(4));
    assert_eq!(columns.get(3), &Value::Integer(5));
    assert_eq!(columns.get(4), &Value::Integer(6));
    assert_eq!(columns.get(5), &Value::Integer(4));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 6);
    assert_eq!(columns.get(0), &Value::Integer(9));
    assert_eq!(columns.get(1), &Value::Integer(9));
    assert_eq!(columns.get(2), &Value::Integer(7));
    assert_eq!(columns.get(3), &Value::Integer(8));
    assert_eq!(columns.get(4), &Value::Integer(9));
    assert_eq!(columns.get(5), &Value::Integer(7));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());
}

#[test]
fn test_select_primary_key() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(id integer primary key, col text);",
        "INSERT INTO example(id, col) VALUES (1, '10');",
        "INSERT INTO example(id, col) VALUES (5, '20');",
        "INSERT INTO example(id, col) VALUES (3, '30');",
    ]);
    let mut conn = Connection::open(file.path()).unwrap();

    let mut stmt = conn.prepare("SELECT * FROM example;").unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(1));
    assert_eq!(columns.get(1), &Value::Text(b"10"));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(3));
    assert_eq!(columns.get(1), &Value::Text(b"30"));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(5));
    assert_eq!(columns.get(1), &Value::Text(b"20"));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());
}

#[test]
fn test_select_filter() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col1, col2, col3);",
        "INSERT INTO example(col1, col2, col3) VALUES (1, 2, 3);",
        "INSERT INTO example(col1, col2, col3) VALUES (4, 5, 6);",
        "INSERT INTO example(col1, col2, col3) VALUES (7, 8, 9);",
    ]);

    let mut conn = Connection::open(file.path()).unwrap();
    let mut stmt = conn
        .prepare("SELECT * FROM example WHERE col2 == 5;")
        .unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 3);
    assert_eq!(columns.get(0), &Value::Integer(4));
    assert_eq!(columns.get(1), &Value::Integer(5));
    assert_eq!(columns.get(2), &Value::Integer(6));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());

    let mut stmt = conn
        .prepare("SELECT col2 FROM example WHERE col2 >= 5;")
        .unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 1);
    assert_eq!(columns.get(0), &Value::Integer(5));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 1);
    assert_eq!(columns.get(0), &Value::Integer(8));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());

    let mut stmt = conn
        .prepare("SELECT col2 FROM example WHERE col2 != 5;")
        .unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 1);
    assert_eq!(columns.get(0), &Value::Integer(2));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 1);
    assert_eq!(columns.get(0), &Value::Integer(8));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());
}

#[test]
fn test_select_filter_eq() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col1, col2, col3);",
        "INSERT INTO example(col1, col2, col3) VALUES ('hello', 2.0, 3);",
        // TODO: col2 = 2 integer?
        "INSERT INTO example(col1, col2, col3) VALUES ('world', 2.0, 9);",
        "INSERT INTO example(col1, col2, col3) VALUES ('hello', 5.0, 9);",
    ]);

    let mut conn = Connection::open(file.path()).unwrap();
    let mut stmt = conn
        .prepare("SELECT rowid, col1 FROM example WHERE col1 == 'hello';")
        .unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(1));
    assert_eq!(columns.get(1), &Value::Text(b"hello"));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(3));
    assert_eq!(columns.get(1), &Value::Text(b"hello"));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());

    let mut stmt = conn
        .prepare("SELECT rowid, col2 FROM example WHERE col2 = 2.0;")
        .unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(1));
    assert_eq!(columns.get(1), &Value::Real(2.0));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(2));
    assert_eq!(columns.get(1), &Value::Real(2.0));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());

    let mut stmt = conn
        .prepare("SELECT rowid, col3 FROM example WHERE col3 == 9;")
        .unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(2));
    assert_eq!(columns.get(1), &Value::Integer(9));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(3));
    assert_eq!(columns.get(1), &Value::Integer(9));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());
}

#[test]
fn test_select_filter_ne() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col1, col2, col3);",
        "INSERT INTO example(col1, col2, col3) VALUES ('hello', 2.0, 3);",
        // TODO: col2 = 2 integer?
        "INSERT INTO example(col1, col2, col3) VALUES ('world', 2.0, 9);",
        "INSERT INTO example(col1, col2, col3) VALUES ('hello', 5.0, 9);",
    ]);

    let mut conn = Connection::open(file.path()).unwrap();
    let mut stmt = conn
        .prepare("SELECT rowid, col1 FROM example WHERE col1 != 'hello';")
        .unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(2));
    assert_eq!(columns.get(1), &Value::Text(b"world"));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());

    let mut stmt = conn
        .prepare("SELECT rowid, col2 FROM example WHERE col2 != 2.0;")
        .unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(3));
    assert_eq!(columns.get(1), &Value::Real(5.0));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());

    let mut stmt = conn
        .prepare("SELECT rowid, col3 FROM example WHERE col3 != 9;")
        .unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(1));
    assert_eq!(columns.get(1), &Value::Integer(3));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());
}

#[test]
fn test_select_filter_with_rowid() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col);",
        "INSERT INTO example(col) VALUES (10);",
        "INSERT INTO example(col) VALUES (20);",
        "INSERT INTO example(col) VALUES (30);",
        "INSERT INTO example(col) VALUES (40);",
    ]);

    let mut conn = Connection::open(file.path()).unwrap();
    let mut stmt = conn
        .prepare("SELECT col, RoWid FROM example WHERE rowid = 2;")
        .unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(20));
    assert_eq!(columns.get(1), &Value::Integer(2));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());
}

#[test]
fn test_select_filter_with_primary_key() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(id integer primary key, col text);",
        "INSERT INTO example(id, col) VALUES (1, '10');",
        "INSERT INTO example(id, col) VALUES (3, '20');",
        "INSERT INTO example(id, col) VALUES (5, '30');",
        "INSERT INTO example(id, col) VALUES (6, '40');",
    ]);
    let mut conn = Connection::open(file.path()).unwrap();

    let mut stmt = conn
        .prepare("SELECT col, RoWid FROM example WHERE id = 3;")
        .unwrap();
    let mut rows = stmt.execute().unwrap();
    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Text(b"20"));
    assert_eq!(columns.get(1), &Value::Integer(3));
    drop(row);
    assert!(rows.next_row().unwrap().is_none());

    let mut stmt = conn
        .prepare("SELECT col, RoWid FROM example WHERE id = 4;")
        .unwrap();
    let mut rows = stmt.execute().unwrap();
    assert!(rows.next_row().unwrap().is_none());
}

#[test]
fn test_select_with_index() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col1, col2, col3);",
        "CREATE INDEX index1 ON example(col2, col3);",
        "CREATE INDEX index2 ON example(col3);",
        "INSERT INTO example(col1, col2, col3) VALUES (1, 2, 3);",
        "INSERT INTO example(col1, col2, col3) VALUES (4, 5, 6);",
        "INSERT INTO example(col1, col2, col3) VALUES (7, 8, 9);",
        "INSERT INTO example(col1, col2, col3) VALUES (10, 5, 2);",
        "INSERT INTO example(col1, col2, col3) VALUES (3, 3, 3);",
    ]);

    let mut conn = Connection::open(file.path()).unwrap();
    let mut stmt = conn
        .prepare("SELECT * FROM example WHERE col2 == 5;")
        .unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 3);
    assert_eq!(columns.get(0), &Value::Integer(10));
    assert_eq!(columns.get(1), &Value::Integer(5));
    assert_eq!(columns.get(2), &Value::Integer(2));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 3);
    assert_eq!(columns.get(0), &Value::Integer(4));
    assert_eq!(columns.get(1), &Value::Integer(5));
    assert_eq!(columns.get(2), &Value::Integer(6));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());

    let mut stmt = conn
        .prepare("SELECT * FROM example WHERE col3 == 6;")
        .unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 3);
    assert_eq!(columns.get(0), &Value::Integer(4));
    assert_eq!(columns.get(1), &Value::Integer(5));
    assert_eq!(columns.get(2), &Value::Integer(6));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());

    let mut stmt = conn
        .prepare("SELECT * FROM example WHERE col3 == 3;")
        .unwrap();
    let mut rows = stmt.execute().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 3);
    assert_eq!(columns.get(0), &Value::Integer(1));
    assert_eq!(columns.get(1), &Value::Integer(2));
    assert_eq!(columns.get(2), &Value::Integer(3));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 3);
    assert_eq!(columns.get(0), &Value::Integer(3));
    assert_eq!(columns.get(1), &Value::Integer(3));
    assert_eq!(columns.get(2), &Value::Integer(3));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());
}
