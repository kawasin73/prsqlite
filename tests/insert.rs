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

mod common;

use common::*;
use prsqlite::Connection;
use prsqlite::Value;

#[test]
fn test_insert() {
    let file = create_sqlite_database(&["CREATE TABLE example(col1, col2, col3);"]);
    let conn = Connection::open(file.path()).unwrap();

    let stmt = conn
        .prepare("INSERT INTO example (col1, col2, col3) VALUES (0, 1, 2);")
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 1);

    let stmt = conn
        .prepare(
            "INSERT INTO example (col1, col2, col3) VALUES (1234.5, 'hello', x'313233'), (3, 4, 5);",
        )
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 2);

    let mut long_text = String::new();
    for _ in 0..100 {
        long_text.push_str("hello world ");
    }
    let stmt = conn
        .prepare(&format!(
            "INSERT INTO example (col2, col1) VALUES ('{long_text}', 10), (NULL, NULL);"
        ))
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 2);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        &[
            &[
                Value::Integer(1),
                Value::Integer(0),
                Value::Integer(1),
                Value::Integer(2),
            ],
            &[
                Value::Integer(2),
                Value::Real(1234.5),
                Value::Text(b"hello".as_slice().into()),
                Value::Blob([0x31, 0x32, 0x33].as_slice().into()),
            ],
            &[
                Value::Integer(3),
                Value::Integer(3),
                Value::Integer(4),
                Value::Integer(5),
            ],
            &[
                Value::Integer(4),
                Value::Integer(10),
                Value::Text(long_text.as_bytes().into()),
                Value::Null,
            ],
            &[Value::Integer(5), Value::Null, Value::Null, Value::Null],
        ],
        "SELECT rowid, * FROM example;",
        &test_conn,
        &conn,
    )
}

#[test]
fn test_insert_per_pagesize() {
    // TODO: Other page sizes 512 ~ 65536.
    for pagesize in [512, 4096, 65536] {
        let pagesize_pragma = format!("PRAGMA page_size = {};", pagesize);
        let file = create_sqlite_database(&[&pagesize_pragma, "CREATE TABLE example(col);"]);
        let conn = Connection::open(file.path()).unwrap();

        let stmt = conn
            .prepare("INSERT INTO example (col) VALUES (123);")
            .unwrap();
        assert_eq!(stmt.execute().unwrap(), 1);

        // TODO: overflow
        // TODO: balance pages

        let test_conn = rusqlite::Connection::open(file.path()).unwrap();
        assert_same_results(
            &[&[Value::Integer(123)]],
            "SELECT col FROM example;",
            &test_conn,
            &conn,
        )
    }
}

#[test]
fn test_insert_with_rowid() {
    let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
    let conn = Connection::open(file.path()).unwrap();

    let stmt = conn
        .prepare("INSERT INTO example (rowid, col) VALUES (-10, 2), (10, 5);")
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 2);

    let stmt = conn
        .prepare("INSERT INTO example (rowid, col) VALUES (2, 4), (-11, 1), (11, 6), (0, 3);")
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 4);

    // no rowid inserts to the tail.
    let stmt = conn
        .prepare("INSERT INTO example (col) VALUES (7);")
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 1);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        &[
            &[Value::Integer(-11), Value::Integer(1)],
            &[Value::Integer(-10), Value::Integer(2)],
            &[Value::Integer(0), Value::Integer(3)],
            &[Value::Integer(2), Value::Integer(4)],
            &[Value::Integer(10), Value::Integer(5)],
            &[Value::Integer(11), Value::Integer(6)],
            &[Value::Integer(12), Value::Integer(7)],
        ],
        "SELECT rowid, * FROM example;",
        &test_conn,
        &conn,
    )
}

#[test]
fn test_insert_into_existing_table() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col);",
        "INSERT INTO example(rowid, col) VALUES (1, 1);",
        "INSERT INTO example(rowid, col) VALUES (10, 2);",
    ]);
    let conn = Connection::open(file.path()).unwrap();

    let stmt = conn
        .prepare("INSERT INTO example (rowid, col) VALUES (2, 3), (8, 4);")
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 2);

    let stmt = conn
        .prepare("INSERT INTO example (col) VALUES (5);")
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 1);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        &[
            &[Value::Integer(1), Value::Integer(1)],
            &[Value::Integer(2), Value::Integer(3)],
            &[Value::Integer(8), Value::Integer(4)],
            &[Value::Integer(10), Value::Integer(2)],
            &[Value::Integer(11), Value::Integer(5)],
        ],
        "SELECT rowid, * FROM example;",
        &test_conn,
        &conn,
    )
}

#[test]
fn test_insert_rowid_conflict() {
    let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
    let conn = Connection::open(file.path()).unwrap();

    let stmt = conn
        .prepare("INSERT INTO example (col) VALUES (123);")
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 1);

    let stmt = conn
        .prepare("INSERT INTO example (rowid, col) VALUES (1, 456), (2, 567);")
        .unwrap();
    assert!(stmt.execute().is_err());

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        &[&[Value::Integer(1), Value::Integer(123)]],
        "SELECT rowid, * FROM example;",
        &test_conn,
        &conn,
    )
}

#[test]
fn test_insert_multiple_statements() {
    let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
    let conn = Connection::open(file.path()).unwrap();

    let stmt_i1 = conn
        .prepare("INSERT INTO example (col) VALUES (123);")
        .unwrap();
    let stmt_s1 = conn.prepare("SELECT * FROM example;").unwrap();
    let stmt_i2 = conn
        .prepare("INSERT INTO example (col) VALUES (456);")
        .unwrap();
    let stmt_s2 = conn.prepare("SELECT * FROM example;").unwrap();
    let stmt_i3 = conn
        .prepare("INSERT INTO example (col) VALUES (789);")
        .unwrap();

    assert_eq!(stmt_i1.execute().unwrap(), 1);

    let mut rows = stmt_s1.query().unwrap();
    assert_same_result_prsqlite!(rows, [Value::Integer(123)], "");
    assert!(rows.next_row().unwrap().is_none());
    drop(rows);
    let mut rows = stmt_s2.query().unwrap();
    assert_same_result_prsqlite!(rows, [Value::Integer(123)], "");
    assert!(rows.next_row().unwrap().is_none());
    drop(rows);

    assert_eq!(stmt_i2.execute().unwrap(), 1);

    let mut rows = stmt_s1.query().unwrap();
    assert_same_result_prsqlite!(rows, [Value::Integer(123)], "");
    assert_same_result_prsqlite!(rows, [Value::Integer(456)], "");
    assert!(rows.next_row().unwrap().is_none());
    let mut rows = stmt_s2.query().unwrap();
    // INSERT fails while SELECT is running.
    assert!(stmt_i3.execute().is_err());
    assert_same_result_prsqlite!(rows, [Value::Integer(123)], "");
    assert_same_result_prsqlite!(rows, [Value::Integer(456)], "");
    assert!(rows.next_row().unwrap().is_none());
}

#[test]
fn test_insert_reuse_statement() {
    let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
    let conn = Connection::open(file.path()).unwrap();

    let stmt1 = conn
        .prepare("INSERT INTO example (col) VALUES (123);")
        .unwrap();
    assert_eq!(stmt1.execute().unwrap(), 1);
    assert_eq!(stmt1.execute().unwrap(), 1);
    assert_eq!(stmt1.execute().unwrap(), 1);

    let stmt2 = conn
        .prepare("INSERT INTO example (col) VALUES (456), (789);")
        .unwrap();
    assert_eq!(stmt2.execute().unwrap(), 2);
    assert_eq!(stmt2.execute().unwrap(), 2);

    assert_eq!(stmt1.execute().unwrap(), 1);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        &[
            &[Value::Integer(123)],
            &[Value::Integer(123)],
            &[Value::Integer(123)],
            &[Value::Integer(456)],
            &[Value::Integer(789)],
            &[Value::Integer(456)],
            &[Value::Integer(789)],
            &[Value::Integer(123)],
        ],
        "SELECT * FROM example;",
        &test_conn,
        &conn,
    )
}
