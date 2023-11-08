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
fn test_delete() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col);",
        "CREATE INDEX index1 ON example(col);",
        "INSERT INTO example (col) VALUES (10);",
        "INSERT INTO example (col) VALUES (20);",
        "INSERT INTO example (col) VALUES (30);",
    ]);
    let conn = Connection::open(file.path()).unwrap();

    let stmt = conn.prepare("DELETE FROM example;").unwrap();
    assert_eq!(stmt.execute().unwrap(), 3);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(&[], "SELECT * FROM example;", &test_conn, &conn);

    assert_eq!(stmt.execute().unwrap(), 0);

    let insert_stmt = conn
        .prepare("INSERT INTO example (col) VALUES (0), (1);")
        .unwrap();
    assert_eq!(insert_stmt.execute().unwrap(), 2);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        &[&[Some(&Value::Integer(0))], &[Some(&Value::Integer(1))]],
        "SELECT * FROM example;",
        &test_conn,
        &conn,
    );
}

#[test]
fn test_delete_all_multiple_level() {
    let mut stmts = vec![
        "PRAGMA page_size = 512;",
        "CREATE TABLE example(col);",
        "CREATE INDEX index1 ON example(col);",
    ];
    let insert_stmt_string = format!("INSERT INTO example(col) VALUES (x'{}');", "11".repeat(100));
    for _ in 0..1000 {
        stmts.push(&insert_stmt_string);
    }
    let file = create_sqlite_database(&stmts);
    let conn = Connection::open(file.path()).unwrap();

    let stmt = conn.prepare("DELETE FROM example;").unwrap();
    assert_eq!(stmt.execute().unwrap(), 1000);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(&[], "SELECT * FROM example;", &test_conn, &conn);

    assert_eq!(stmt.execute().unwrap(), 0);

    let insert_stmt = conn.prepare(&insert_stmt_string).unwrap();
    for _ in 0..1000 {
        assert_eq!(insert_stmt.execute().unwrap(), 1);
    }

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    let v = Value::Blob(vec![0x11; 100].into());
    let row = [Some(&v)];
    let mut expected = Vec::with_capacity(1000);
    for _ in 0..1000 {
        expected.push(row.as_slice());
    }
    assert_same_results(
        expected.as_slice(),
        "SELECT * FROM example;",
        &test_conn,
        &conn,
    );
}

#[test]
fn test_delete_after_insert() {
    let file = create_sqlite_database(&[
        "PRAGMA page_size = 512;",
        "CREATE TABLE example(col);",
        "CREATE INDEX index1 ON example(col);",
    ]);
    let conn = Connection::open(file.path()).unwrap();

    let insert_stmt_string = format!("INSERT INTO example(col) VALUES (x'{}');", "11".repeat(50));
    let insert_stmt = conn.prepare(&insert_stmt_string).unwrap();
    for _ in 0..2000 {
        assert_eq!(insert_stmt.execute().unwrap(), 1);
    }
    let v = Value::Blob(vec![0x11; 50].into());
    let row = [Some(&v)];
    let mut expected = Vec::with_capacity(2000);
    for _ in 0..2000 {
        expected.push(row.as_slice());
    }
    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        expected.as_slice(),
        "SELECT * FROM example;",
        &test_conn,
        &conn,
    );
    let original_file_size = file.as_file().metadata().unwrap().len();

    let stmt = conn.prepare("DELETE FROM example;").unwrap();
    assert_eq!(stmt.execute().unwrap(), 2000);
    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(&[], "SELECT * FROM example;", &test_conn, &conn);

    for _ in 0..2000 {
        assert_eq!(insert_stmt.execute().unwrap(), 1);
    }
    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        expected.as_slice(),
        "SELECT * FROM example;",
        &test_conn,
        &conn,
    );
    assert_eq!(file.as_file().metadata().unwrap().len(), original_file_size);
}

#[test]
fn test_delete_after_insert_with_overflow_payloads() {
    let file = create_sqlite_database(&[
        "PRAGMA page_size = 512;",
        "CREATE TABLE example(col);",
        "CREATE INDEX index1 ON example(col);",
    ]);
    let conn = Connection::open(file.path()).unwrap();

    // Creates 1 overflow payload page.
    let insert_stmt_string = format!("INSERT INTO example(col) VALUES (x'{}');", "11".repeat(512));
    let insert_stmt512 = conn.prepare(&insert_stmt_string).unwrap();
    for _ in 0..500 {
        assert_eq!(insert_stmt512.execute().unwrap(), 1);
    }
    // Creates 2 overflow payload page.
    let insert_stmt_string = format!(
        "INSERT INTO example(col) VALUES (x'{}');",
        "22".repeat(1024)
    );
    let insert_stmt1024 = conn.prepare(&insert_stmt_string).unwrap();
    for _ in 0..500 {
        assert_eq!(insert_stmt1024.execute().unwrap(), 1);
    }
    let v512 = Value::Blob(vec![0x11; 512].into());
    let row512 = [Some(&v512)];
    let mut expected = Vec::with_capacity(1000);
    for _ in 0..500 {
        expected.push(row512.as_slice());
    }
    let v1024 = Value::Blob(vec![0x22; 1024].into());
    let row1024 = [Some(&v1024)];
    for _ in 0..500 {
        expected.push(row1024.as_slice());
    }
    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        expected.as_slice(),
        "SELECT * FROM example;",
        &test_conn,
        &conn,
    );
    let original_file_size = file.as_file().metadata().unwrap().len();

    let stmt = conn.prepare("DELETE FROM example;").unwrap();
    assert_eq!(stmt.execute().unwrap(), 1000);
    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(&[], "SELECT * FROM example;", &test_conn, &conn);

    for _ in 0..500 {
        assert_eq!(insert_stmt512.execute().unwrap(), 1);
    }
    for _ in 0..500 {
        assert_eq!(insert_stmt1024.execute().unwrap(), 1);
    }
    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        expected.as_slice(),
        "SELECT * FROM example;",
        &test_conn,
        &conn,
    );
    assert_eq!(file.as_file().metadata().unwrap().len(), original_file_size);
}
