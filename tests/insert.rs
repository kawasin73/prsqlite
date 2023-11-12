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
use prsqlite::Error;
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
                Some(&Value::Integer(1)),
                Some(&Value::Integer(0)),
                Some(&Value::Integer(1)),
                Some(&Value::Integer(2)),
            ],
            &[
                Some(&Value::Integer(2)),
                Some(&Value::Real(1234.5)),
                Some(&Value::Text(b"hello".as_slice().into())),
                Some(&Value::Blob([0x31, 0x32, 0x33].as_slice().into())),
            ],
            &[
                Some(&Value::Integer(3)),
                Some(&Value::Integer(3)),
                Some(&Value::Integer(4)),
                Some(&Value::Integer(5)),
            ],
            &[
                Some(&Value::Integer(4)),
                Some(&Value::Integer(10)),
                Some(&Value::Text(long_text.as_bytes().into())),
                None,
            ],
            &[Some(&Value::Integer(5)), None, None, None],
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
            &[&[Some(&Value::Integer(123))]],
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

    // NULL rowid is treated as the tail.
    let stmt = conn
        .prepare("INSERT INTO example (rowid, col) VALUES (NULL, 8);")
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 1);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        &[
            &[Some(&Value::Integer(-11)), Some(&Value::Integer(1))],
            &[Some(&Value::Integer(-10)), Some(&Value::Integer(2))],
            &[Some(&Value::Integer(0)), Some(&Value::Integer(3))],
            &[Some(&Value::Integer(2)), Some(&Value::Integer(4))],
            &[Some(&Value::Integer(10)), Some(&Value::Integer(5))],
            &[Some(&Value::Integer(11)), Some(&Value::Integer(6))],
            &[Some(&Value::Integer(12)), Some(&Value::Integer(7))],
            &[Some(&Value::Integer(13)), Some(&Value::Integer(8))],
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
            &[Some(&Value::Integer(1)), Some(&Value::Integer(1))],
            &[Some(&Value::Integer(2)), Some(&Value::Integer(3))],
            &[Some(&Value::Integer(8)), Some(&Value::Integer(4))],
            &[Some(&Value::Integer(10)), Some(&Value::Integer(2))],
            &[Some(&Value::Integer(11)), Some(&Value::Integer(5))],
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
        .prepare("INSERT INTO example (rowid, col) VALUES (1, 234), (2, 345);")
        .unwrap();
    assert!(matches!(
        stmt.execute().err().unwrap(),
        Error::UniqueConstraintViolation
    ));

    let stmt = conn
        .prepare("INSERT INTO example (rowid, col) VALUES (2, 456), (1, 567);")
        .unwrap();
    assert!(matches!(
        stmt.execute().err().unwrap(),
        Error::UniqueConstraintViolation
    ));

    let stmt = conn
        .prepare("INSERT INTO example (rowid, col) VALUES (2, 678), (2, 789);")
        .unwrap();
    assert!(matches!(
        stmt.execute().err().unwrap(),
        Error::UniqueConstraintViolation
    ));

    let stmt = conn
        .prepare("INSERT INTO example (col) VALUES (890);")
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 1);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        &[
            &[Some(&Value::Integer(1)), Some(&Value::Integer(123))],
            &[Some(&Value::Integer(2)), Some(&Value::Integer(890))],
        ],
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
    assert_same_result_prsqlite!(rows, [Some(&Value::Integer(123))], "");
    assert!(rows.next_row().unwrap().is_none());
    drop(rows);
    let mut rows = stmt_s2.query().unwrap();
    assert_same_result_prsqlite!(rows, [Some(&Value::Integer(123))], "");
    assert!(rows.next_row().unwrap().is_none());
    drop(rows);

    assert_eq!(stmt_i2.execute().unwrap(), 1);

    let mut rows = stmt_s1.query().unwrap();
    assert_same_result_prsqlite!(rows, [Some(&Value::Integer(123))], "");
    assert_same_result_prsqlite!(rows, [Some(&Value::Integer(456))], "");
    assert!(rows.next_row().unwrap().is_none());
    let mut rows = stmt_s2.query().unwrap();
    // INSERT fails while SELECT is running.
    assert!(stmt_i3.execute().is_err());
    assert_same_result_prsqlite!(rows, [Some(&Value::Integer(123))], "");
    assert_same_result_prsqlite!(rows, [Some(&Value::Integer(456))], "");
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
            &[Some(&Value::Integer(123))],
            &[Some(&Value::Integer(123))],
            &[Some(&Value::Integer(123))],
            &[Some(&Value::Integer(456))],
            &[Some(&Value::Integer(789))],
            &[Some(&Value::Integer(456))],
            &[Some(&Value::Integer(789))],
            &[Some(&Value::Integer(123))],
        ],
        "SELECT * FROM example;",
        &test_conn,
        &conn,
    )
}

#[test]
fn test_insert_overflow() {
    let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
    let conn = Connection::open(file.path()).unwrap();

    let mut long_text = String::new();
    for _ in 0..1000 {
        long_text.push_str("hello world ");
    }

    let stmt = conn
        .prepare(&format!(
            "INSERT INTO example (col) VALUES ('{long_text}');"
        ))
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 1);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        &[&[Some(&Value::Text(long_text.as_bytes().into()))]],
        "SELECT * FROM example;",
        &test_conn,
        &conn,
    )
}

#[test]
fn test_insert_1_cell_per_table_page_no_overflow() {
    let file = create_sqlite_database(&["PRAGMA page_size = 512;", "CREATE TABLE example(col);"]);
    let conn = Connection::open(file.path()).unwrap();
    const N_ENTRIES: usize = 128;

    let insert_stmt_string = format!("INSERT INTO example(col) VALUES (x'{}');", "11".repeat(412));
    let insert_stmt = conn.prepare(&insert_stmt_string).unwrap();
    for _ in 0..N_ENTRIES {
        assert_eq!(insert_stmt.execute().unwrap(), 1);
    }
    let v = Value::Blob(vec![0x11; 412].into());
    let row = [Some(&v)];
    let mut expected = Vec::with_capacity(N_ENTRIES);
    for _ in 0..N_ENTRIES {
        expected.push(row.as_slice());
    }
    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        expected.as_slice(),
        "SELECT * FROM example;",
        &test_conn,
        &conn,
    );
}

#[test]
fn test_insert_overflow_index() {
    let file = create_sqlite_database(&[
        "PRAGMA page_size = 512;",
        "CREATE TABLE example(col);",
        // "CREATE INDEX index1 ON example(col);",
    ]);
    let conn = Connection::open(file.path()).unwrap();

    let insert_stmt_string = format!("INSERT INTO example(col) VALUES (x'{}');", "11".repeat(412));
    let insert_stmt = conn.prepare(&insert_stmt_string).unwrap();
    for _ in 0..1000 {
        assert_eq!(insert_stmt.execute().unwrap(), 1);
    }
    let v = Value::Blob(vec![0x11; 412].into());
    let row = [Some(&v)];
    let mut expected = Vec::with_capacity(1000);
    for _ in 0..1000 {
        expected.push(row.as_slice());
    }
    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        expected.as_slice(),
        "SELECT * FROM example;",
        &test_conn,
        &conn,
    );
}

#[test]
fn test_insert_freeblock() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col);",
        "INSERT INTO example (col) VALUES (x'01');",
        "INSERT INTO example (col) VALUES (x'0202');",
        "INSERT INTO example (col) VALUES (x'030303');",
        "INSERT INTO example (col) VALUES (x'04040404');",
        "INSERT INTO example (col) VALUES (x'0505050505');",
        "INSERT INTO example (col) VALUES (x'060606060606');",
        "INSERT INTO example (col) VALUES (x'07070707070707');",
        "INSERT INTO example (col) VALUES (x'0808080808080808');",
        "INSERT INTO example (col) VALUES (x'090909090909090909');",
        "INSERT INTO example (col) VALUES (x'0a0a0a0a0a0a0a0a0a0a');",
        "DELETE FROM example WHERE rowid IN (1, 3, 5, 7, 9);",
    ]);
    let conn = Connection::open(file.path()).unwrap();

    let stmt = conn
        .prepare("INSERT INTO example (col) VALUES (x'0b0b0b0b0b0b0b0b0b0b0b');")
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 1);

    let stmt = conn
        .prepare("INSERT INTO example (col) VALUES (x'090909090909090909');")
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 1);

    let stmt = conn
        .prepare("INSERT INTO example (col) VALUES (x'01');")
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 1);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        &[
            &[Some(&Value::Blob([0x02, 0x02].as_slice().into()))],
            &[Some(&Value::Blob(
                [0x04, 0x04, 0x04, 0x04].as_slice().into(),
            ))],
            &[Some(&Value::Blob(
                [0x06, 0x06, 0x06, 0x06, 0x06, 0x06].as_slice().into(),
            ))],
            &[Some(&Value::Blob(
                [0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08]
                    .as_slice()
                    .into(),
            ))],
            &[Some(&Value::Blob(
                [0x0a, 0x0a, 0x0a, 0x0a, 0x0a, 0x0a, 0x0a, 0x0a, 0x0a, 0x0a]
                    .as_slice()
                    .into(),
            ))],
            &[Some(&Value::Blob(
                [
                    0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
                ]
                .as_slice()
                .into(),
            ))],
            &[Some(&Value::Blob(
                [0x09, 0x09, 0x09, 0x09, 0x09, 0x09, 0x09, 0x09, 0x09]
                    .as_slice()
                    .into(),
            ))],
            &[Some(&Value::Blob([0x01].as_slice().into()))],
        ],
        "SELECT col FROM example;",
        &test_conn,
        &conn,
    )
}

#[test]
fn test_insert_split() {
    let file = create_sqlite_database(&[
        "PRAGMA page_size = 512;",
        "CREATE TABLE example(col);",
        "CREATE INDEX index1 ON example(col);",
    ]);
    let conn = Connection::open(file.path()).unwrap();
    let magic_v = "abc".repeat(50);
    let magic_v_overflow = "hello".repeat(100);

    for i in 0..5 {
        for j in 0..3 {
            for k in 0..500 {
                let rowid = 15 * k + 5 * j + i;
                conn.prepare(&format!(
                    "INSERT INTO example (rowid, col) VALUES ({}, '{}{}{}');",
                    rowid, rowid, &magic_v, rowid
                ))
                .unwrap()
                .execute()
                .unwrap();
            }
        }
    }
    for i in 0..5 {
        for j in 0..3 {
            for k in 0..50 {
                let rowid = 5 * 3 * 500 + 15 * k + 5 * j + i;
                conn.prepare(&format!(
                    "INSERT INTO example (rowid, col) VALUES ({}, '{}{}{}');",
                    rowid, rowid, &magic_v_overflow, rowid
                ))
                .unwrap()
                .execute()
                .unwrap();
            }
        }
    }

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    let sql = "SELECT rowid, col FROM example;";
    let mut test_stmt = test_conn.prepare(sql).unwrap();
    let mut test_rows = test_stmt.query([]).unwrap();
    let stmt = conn.prepare(sql).unwrap();
    let mut rows = stmt.query().unwrap();
    for rowid in 0..3 * 5 * 500 {
        let expected = format!("{}{}{}", rowid, &magic_v, rowid);
        let test_row = test_rows.next().unwrap().unwrap();
        assert_eq!(test_row.get::<_, i64>(0).unwrap(), rowid);
        assert_eq!(&test_row.get::<_, String>(1).unwrap(), &expected);

        let row = rows.next_row().unwrap().unwrap();
        let columns = row.parse().unwrap();
        assert_eq!(columns.len(), 2);
        assert_eq!(columns.get(0), Some(&Value::Integer(rowid)));
        assert_eq!(
            columns.get(1),
            Some(&Value::Text(expected.as_bytes().into()))
        );
    }
    for i in 0..3 * 5 * 50 {
        let rowid = 3 * 5 * 500 + i;
        let expected = format!("{}{}{}", rowid, &magic_v_overflow, rowid);
        let test_row = test_rows.next().unwrap().unwrap();
        assert_eq!(test_row.get::<_, i64>(0).unwrap(), rowid);
        assert_eq!(&test_row.get::<_, String>(1).unwrap(), &expected);

        let row = rows.next_row().unwrap().unwrap();
        let columns = row.parse().unwrap();
        assert_eq!(columns.len(), 2);
        assert_eq!(columns.get(0), Some(&Value::Integer(rowid)));
        assert_eq!(
            columns.get(1),
            Some(&Value::Text(expected.as_bytes().into()))
        );
    }
    assert!(test_rows.next().unwrap().is_none());
    assert!(rows.next_row().unwrap().is_none());

    for rowid in 0..3 * 5 * 500 {
        assert_same_results(
            &[&[Some(&Value::Integer(rowid))]],
            &format!(
                "SELECT rowid from example WHERE col = '{}{}{}';",
                rowid, &magic_v, rowid
            ),
            &test_conn,
            &conn,
        );
    }
    for i in 0..3 * 5 * 50 {
        let rowid = 3 * 5 * 500 + i;
        assert_same_results(
            &[&[Some(&Value::Integer(rowid))]],
            &format!(
                "SELECT rowid from example WHERE col = '{}{}{}';",
                rowid, &magic_v_overflow, rowid
            ),
            &test_conn,
            &conn,
        );
    }
}

#[test]
fn test_insert_index() {
    let file = create_sqlite_database(&[
        "PRAGMA page_size = 512;",
        "CREATE TABLE example(col1, col2);",
        "CREATE INDEX index1 ON example(col1);",
        "CREATE INDEX index2 ON example(col2, col1);",
    ]);
    let conn = Connection::open(file.path()).unwrap();

    assert_eq!(
        conn.prepare("INSERT INTO example (col1, col2) VALUES (1, 2);")
            .unwrap()
            .execute()
            .unwrap(),
        1
    );
    assert_eq!(
        conn.prepare("INSERT INTO example (col1, col2) VALUES (1, 3), (3, 3), (2, 3), (1, 3);")
            .unwrap()
            .execute()
            .unwrap(),
        4
    );
    assert_eq!(
        conn.prepare("INSERT INTO example (col2) VALUES (3);")
            .unwrap()
            .execute()
            .unwrap(),
        1
    );

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    let sql = "SELECT rowid FROM example WHERE col1 = 1;";
    let rowids = [1, 2, 5];
    assert_eq!(&load_rowids(&conn, sql), &rowids, "{}", sql);
    assert_eq!(&load_test_rowids(&test_conn, sql), &rowids, "{}", sql);

    let sql = "SELECT rowid FROM example WHERE col2 = 3;";
    let rowids = [6, 2, 5, 4, 3];
    assert_eq!(&load_rowids(&conn, sql), &rowids, "{}", sql);
    assert_eq!(&load_test_rowids(&test_conn, sql), &rowids, "{}", sql);

    let sql = "SELECT rowid FROM example WHERE col2 = 3 AND col1 = 1;";
    let rowids = [2, 5];
    // TODO: Support multiple conditions in prsqlite.
    assert_eq!(&load_test_rowids(&test_conn, sql), &rowids, "{}", sql);
}

#[test]
fn test_insert_rowid_type_affinity() {
    let file = create_sqlite_database(&["CREATE TABLE example(col);"]);
    let conn = Connection::open(file.path()).unwrap();

    let stmt = conn
        .prepare("INSERT INTO example (rowid, col) VALUES (NULL, NULL);")
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 1);

    let stmt = conn
        .prepare("INSERT INTO example (rowid, col) VALUES (2, 2);")
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 1);

    let stmt = conn
        .prepare("INSERT INTO example (rowid, col) VALUES (4.0, 4.0);")
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 1);

    let stmt = conn
        .prepare("INSERT INTO example (rowid, col) VALUES ('10', '10');")
        .unwrap();
    assert_eq!(stmt.execute().unwrap(), 1);

    let stmt = conn
        .prepare("INSERT INTO example (rowid, col) VALUES (12.1, 12.1);")
        .unwrap();
    assert!(matches!(
        stmt.execute().err().unwrap(),
        Error::DataTypeMismatch
    ));

    let stmt = conn
        .prepare("INSERT INTO example (rowid, col) VALUES ('14a', '14a');")
        .unwrap();
    assert!(matches!(
        stmt.execute().err().unwrap(),
        Error::DataTypeMismatch
    ));

    let stmt = conn
        .prepare("INSERT INTO example (rowid, col) VALUES ('14a', '14a');")
        .unwrap();
    assert!(matches!(
        stmt.execute().err().unwrap(),
        Error::DataTypeMismatch
    ));

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        &[
            &[Some(&Value::Integer(1)), None],
            &[Some(&Value::Integer(2)), Some(&Value::Integer(2))],
            &[Some(&Value::Integer(4)), Some(&Value::Real(4.0))],
            &[
                Some(&Value::Integer(10)),
                Some(&Value::Text(b"10".as_slice().into())),
            ],
        ],
        "SELECT rowid, * FROM example;",
        &test_conn,
        &conn,
    )
}

/// Test case is from https://www.sqlite.org/datatype3.html#column_affinity_behavior_example
#[test]
fn test_insert_type_affinity() {
    let file = create_sqlite_database(&[
        "CREATE TABLE t1(t TEXT, nu NUMERIC, i INTEGER, r REAL, no BLOB);",
    ]);
    let conn = Connection::open(file.path()).unwrap();

    assert_eq!(
        conn.prepare(
            "INSERT INTO t1(t, nu, i, r, no) VALUES('500.0', '500.0', '500.0', '500.0', '500.0');"
        )
        .unwrap()
        .execute()
        .unwrap(),
        1
    );

    assert_eq!(
        conn.prepare("INSERT INTO t1(t, nu, i, r, no) VALUES(500.0, 500.0, 500.0, 500.0, 500.0);")
            .unwrap()
            .execute()
            .unwrap(),
        1
    );

    assert_eq!(
        conn.prepare("INSERT INTO t1(t, nu, i, r, no) VALUES(500, 500, 500, 500, 500);")
            .unwrap()
            .execute()
            .unwrap(),
        1
    );

    assert_eq!(
        conn.prepare(
            "INSERT INTO t1(t, nu, i, r, no) VALUES(x'0500', x'0500', x'0500', x'0500', x'0500');"
        )
        .unwrap()
        .execute()
        .unwrap(),
        1
    );

    assert_eq!(
        conn.prepare("INSERT INTO t1(t, nu, i, r, no) VALUES(NULL,NULL,NULL,NULL,NULL);")
            .unwrap()
            .execute()
            .unwrap(),
        1
    );

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    assert_same_results(
        &[
            &[
                Some(&Value::Text(b"500.0".as_slice().into())),
                Some(&Value::Integer(500)),
                Some(&Value::Integer(500)),
                Some(&Value::Real(500.0)),
                Some(&Value::Text(b"500.0".as_slice().into())),
            ],
            &[
                Some(&Value::Text(b"500".as_slice().into())),
                Some(&Value::Integer(500)),
                Some(&Value::Integer(500)),
                Some(&Value::Real(500.0)),
                Some(&Value::Real(500.0)),
            ],
            &[
                Some(&Value::Text(b"500".as_slice().into())),
                Some(&Value::Integer(500)),
                Some(&Value::Integer(500)),
                Some(&Value::Real(500.0)),
                Some(&Value::Integer(500)),
            ],
            &[
                Some(&Value::Blob([0x05, 0x00].as_slice().into())),
                Some(&Value::Blob([0x05, 0x00].as_slice().into())),
                Some(&Value::Blob([0x05, 0x00].as_slice().into())),
                Some(&Value::Blob([0x05, 0x00].as_slice().into())),
                Some(&Value::Blob([0x05, 0x00].as_slice().into())),
            ],
            &[None, None, None, None, None],
        ],
        "SELECT * FROM t1;",
        &test_conn,
        &conn,
    )
}
