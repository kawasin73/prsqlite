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
    let stmt = conn.prepare("SELECT * FROM example3;").unwrap();
    let mut rows = stmt.query().unwrap();

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
    assert_eq!(columns.get(2), &Value::Text(b"hello".as_slice().into()));
    assert_eq!(columns.get(3), &Value::Null);
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 3);
    assert_eq!(
        columns.get(0),
        &Value::Blob([0xFF; 10000].as_slice().into())
    );
    assert_eq!(columns.get(1), &Value::Integer(20000));
    assert_eq!(columns.get(2), &Value::Null);
    assert_eq!(columns.get(3), &Value::Null);
    drop(row);

    assert!(rows.next_row().unwrap().is_none());
}

#[test]
fn test_select_reuse_statement() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col);",
        "INSERT INTO example(col) VALUES (1), (2);",
    ]);

    let mut conn = Connection::open(file.path()).unwrap();
    let stmt = conn.prepare("SELECT * FROM example;").unwrap();

    let mut rows = stmt.query().unwrap();
    assert_same_result_prsqlite!(rows, [Value::Integer(1)], "");
    assert_same_result_prsqlite!(rows, [Value::Integer(2)], "");
    assert!(rows.next_row().unwrap().is_none());

    let mut rows = stmt.query().unwrap();
    assert_same_result_prsqlite!(rows, [Value::Integer(1)], "");
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
    let stmt = conn.prepare("SELECT col3, col1 FROM example;").unwrap();
    let mut rows = stmt.query().unwrap();

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
    let stmt = conn.prepare("SELECT col, RoWid FROM example;").unwrap();
    let mut rows = stmt.query().unwrap();

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
    let stmt = conn.prepare("SELECT col, Rowid FROM example2;").unwrap();
    let mut rows = stmt.query().unwrap();

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
    let stmt = conn
        .prepare("SELECT col3, col3, *, col1 FROM example;")
        .unwrap();
    let mut rows = stmt.query().unwrap();

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
fn test_select_expression() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col1, col2, col3, col4);",
        "INSERT INTO example(col1, col2, col3, col4) VALUES (1, 2, -3, 4.5);",
    ]);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    let mut conn = Connection::open(file.path()).unwrap();

    for (expected, expr) in [
        // Literals
        (Value::Integer(1), "col1"),
        (Value::Integer(10), "10"),
        (Value::Real(10.0), "10."),
        (Value::Text(b"text".as_slice().into()), "'text'"),
        (
            Value::Blob(b"\x01\x23\x45\x67\x89\xab\xcd\xef".as_slice().into()),
            "x'0123456789abcdef'",
        ),
        (Value::Integer(9223372036854775807), "9223372036854775807"),
        (Value::Real(9223372036854775808.0), "9223372036854775808"),
        (Value::Real(9223372036854775809.0), "9223372036854775809"),
        (Value::Integer(-9223372036854775808), "-9223372036854775808"),
        (Value::Integer(-123), "-123"),
        // Unary operators
        (Value::Integer(-1), "-col1"),
        (Value::Integer(-2), "-col2"),
        (Value::Integer(3), "-col3"),
        (Value::Integer(-2), "-+-+-col2"),
        (Value::Integer(-123), "-+-+-123"),
        (Value::Integer(123), "++++123"),
        (Value::Integer(123), "-+-+123"),
        (Value::Integer(-2), "~col1"),
        (Value::Integer(1), "~~col1"),
        (Value::Integer(-3), "~2.3"),
        (Value::Integer(-124), "~'123'"),
        (Value::Integer(-1), "~'abc'"),
        (Value::Integer(-124), "~x'313233'"),
        (Value::Null, "~NULL"),
        // Comparison operators
        (Value::Integer(1), "10 > col1"),
        (Value::Integer(0), "10 < col1"),
        (Value::Integer(1), "col1 < col2"),
        (Value::Integer(0), "col1 > col2"),
        (Value::Integer(1), "10 == 10"),
        // Cast to numeric
        (Value::Integer(1), "CAST(col1 AS NUMERIC)"),
        (Value::Real(4.5), "CAST(col4 AS NUMERIC)"),
        (Value::Integer(10), "CAST(' 10 ' AS NUMERIC)"),
        (Value::Integer(10), "CAST('10a' AS NUMERIC)"),
        (Value::Integer(10), "CAST('10e.1' AS NUMERIC)"),
        (Value::Integer(0), "CAST('a3' AS NUMERIC)"),
        (Value::Real(101.2), "CAST('10.12e1' AS NUMERIC)"),
        // Cast to integer
        (Value::Integer(1), "CAST(col1 AS INTEGER)"),
        (Value::Integer(4), "CAST(col4 AS INTEGER)"),
        (Value::Integer(10), "CAST(' 10 ' AS INTEGER)"),
        (Value::Integer(10), "CAST('10a' AS INTEGER)"),
        (Value::Integer(10), "CAST('10e.1' AS INTEGER)"),
        (Value::Integer(0), "CAST('a3' AS INTEGER)"),
        (Value::Integer(10), "CAST('10.12e1' AS INTEGER)"),
        // Cast to float
        (Value::Real(1.0), "CAST(col1 AS FLOAT)"),
        (Value::Real(4.5), "CAST(col4 AS FLOAT)"),
        (Value::Real(10.0), "CAST(' 10 ' AS FLOAT)"),
        (Value::Real(10.0), "CAST('10a' AS FLOAT)"),
        (Value::Real(10.0), "CAST('10e.1' AS FLOAT)"),
        (Value::Real(0.0), "CAST('a3' AS FLOAT)"),
        (Value::Real(101.2), "CAST('10.12e1' AS FLOAT)"),
        // Cast to text
        (Value::Text(b"1".to_vec().into()), "CAST(col1 AS TEXT)"),
        (Value::Text(b"-3".to_vec().into()), "CAST(col3 AS TEXT)"),
        (Value::Text(b"4.5".to_vec().into()), "CAST(col4 AS TEXT)"),
        (
            Value::Text(b" 10 ".as_slice().into()),
            "CAST(' 10 ' AS TEXT)",
        ),
        (
            Value::Text(b"12345".as_slice().into()),
            "CAST(x'3132333435' AS TEXT)",
        ),
        // Cast to blob
        (Value::Blob(b"1".to_vec().into()), "CAST(col1 AS BLOB)"),
        (Value::Blob(b"-3".to_vec().into()), "CAST(col3 AS BLOB)"),
        (Value::Blob(b"4.5".to_vec().into()), "CAST(col4 AS BLOB)"),
        (
            Value::Blob(b" 10 ".as_slice().into()),
            "CAST(' 10 ' AS BLOB)",
        ),
        (
            Value::Blob(b"12345".as_slice().into()),
            "CAST(x'3132333435' AS BLOB)",
        ),
        // Collate
        (Value::Integer(1), "col1 COLLATE BINARY"),
        (Value::Integer(2), "2 COLLATE NOCASE"),
        (Value::Real(4.5), "4.5 COLLATE RTRIM"),
        (
            Value::Text(b"abc".as_slice().into()),
            "'abc' COLLATE BINARY",
        ),
        (
            Value::Blob(b"123".as_slice().into()),
            "x'313233' COLLATE BINARY",
        ),
        // Concat
        (Value::Text(b"foobar".to_vec().into()), "'foo' || 'bar'"),
        (
            Value::Text(b"foobarbaz".to_vec().into()),
            "'foo' || 'bar' || 'baz'",
        ),
        (
            Value::Text(b"12345678.9".to_vec().into()),
            "123 || 456 || 78.9",
        ),
        (
            Value::Text(b"123456789".to_vec().into()),
            "123 || x'343536' || '789'",
        ),
    ] {
        let query = format!("SELECT {} FROM example;", expr);
        assert_same_results(&[&[expected]], &query, &test_conn, &mut conn);
    }
}

#[test]
fn test_select_expression_operators() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col1);",
        "INSERT INTO example(col1) VALUES (1);",
    ]);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    let mut conn = Connection::open(file.path()).unwrap();

    for (expected, expr) in [
        (Value::Integer(1), "'a' = 'a' = 1"),
        (Value::Integer(0), "1 = 'a' = 'a'"),
        (Value::Integer(1), "1 < 2 = 1"),
        (Value::Integer(0), "1 = 2 <= 1"),
    ] {
        let query = format!("SELECT {} FROM example;", expr);
        assert_same_results(&[&[expected]], &query, &test_conn, &mut conn);
    }
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

    let stmt = conn.prepare("SELECT * FROM example;").unwrap();
    stmt.query().unwrap();
    let mut rows = stmt.query().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(1));
    assert_eq!(columns.get(1), &Value::Text(b"10".as_slice().into()));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(3));
    assert_eq!(columns.get(1), &Value::Text(b"30".as_slice().into()));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(5));
    assert_eq!(columns.get(1), &Value::Text(b"20".as_slice().into()));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());
}

#[test]
fn test_select_type_conversions_prior_to_comparison() {
    // Test case from https://www.sqlite.org/datatype3.html#comparison_example
    let file = create_sqlite_database(&[
        "CREATE TABLE t1(a TEXT, b NUMERIC, c BLOB, d, e BLOB);",
        "INSERT INTO t1 VALUES ('500', '500', '500', 500, 500);",
    ]);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    let mut conn = Connection::open(file.path()).unwrap();

    for (expected, query) in [
        (vec![0, 1, 1], "SELECT a < 40,   a < 60,   a < 600 FROM t1;"),
        (
            vec![0, 1, 1],
            "SELECT a < '40', a < '60', a < '600' FROM t1;",
        ),
        // numeric affinity is prioritized over text affinity
        (
            vec![0, 0, 1],
            "SELECT a < CAST('40' AS NUMERIC), a < CAST('60' AS NUMERIC), a < CAST('600' AS NUMERIC) FROM t1;",
        ),
        (vec![0, 0, 1], "SELECT b < 40,   b < 60,   b < 600 FROM t1;"),
        (
            vec![0, 0, 1],
            "SELECT b < '40', b < '60', b < '600' FROM t1;",
        ),
        (vec![0, 0, 1], "SELECT b < 40,   b < 60,   b < 600 FROM t1;"),
        // Leading and tailing spaces in text are ignored.
        (
            vec![0, 0, 1],
            "SELECT b < ' 40 ', b < ' 60 ', b < ' 600 ' FROM t1;",
        ),
        (vec![0, 0, 0], "SELECT c < 40,   c < 60,   c < 600 FROM t1;"),
        (
            vec![0, 1, 1],
            "SELECT c < '40', c < '60', c < '600' FROM t1;",
        ),
        (vec![0, 0, 1], "SELECT d < 40,   d < 60,   d < 600 FROM t1;"),
        (
            vec![1, 1, 1],
            "SELECT d < '40', d < '60', d < '600' FROM t1;",
        ),
        // no affinity is converted to text
        (
            vec![0, 1, 1],
            "SELECT 500 < CAST('40' AS TEXT), 500 < CAST('60' AS TEXT), 500 < CAST('600' AS TEXT) FROM t1;",
        ),
        // blob affinity is not converted to text
        (
            vec![1, 1, 1],
            "SELECT e < CAST('40' AS TEXT), e < CAST('60' AS TEXT), e < CAST('600' AS TEXT) FROM t1;",
        ),
        // Concat has no affinity
        (
            vec![1, 1],
            "SELECT 123 < '12' || 3, 123 < CAST('12' AS TEXT) || CAST('3' AS TEXT) FROM t1;",
        ),
    ] {
        let mut stmt = test_conn.prepare(query).unwrap();
        let mut rows = stmt.query([]).unwrap();
        let row = rows.next().unwrap().unwrap();
        let result: Vec<i64> = (0..expected.len())
            .map(|i| {
                let v: i64 = row.get(i).unwrap();
                v
            })
            .collect();
        assert_eq!(result, expected, "query: {}", query);

        let stmt = conn.prepare(query).unwrap();
        let mut rows = stmt.query().unwrap();
        let row = rows.next_row().unwrap().unwrap();
        let columns = row.parse().unwrap();
        assert_eq!(columns.len(), expected.len());
        let columns = columns
            .iter()
            .map(|v| {
                let Value::Integer(i) = *v else {
                    unreachable!()
                };
                i
            })
            .collect::<Vec<_>>();
        assert_eq!(columns, expected, "query: {}", query);
    }
}

#[test]
fn test_select_collation_sequence() {
    // Test case from https://www.sqlite.org/datatype3.html#collation_sequence_examples
    let file = create_sqlite_database(&[
        "CREATE TABLE t1(x INTEGER PRIMARY KEY, a, b COLLATE BINARY, c COLLATE RTRIM, d COLLATE NOCASE);",
        "INSERT INTO t1 VALUES(1,'abc','abc', 'abc  ','abc');",
        "INSERT INTO t1 VALUES(2,'abc','abc', 'abc',  'ABC');",
        "INSERT INTO t1 VALUES(3,'abc','abc', 'abc ', 'Abc');",
        "INSERT INTO t1 VALUES(4,'abc','abc ','ABC',  'abc');",
    ]);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    let mut conn = Connection::open(file.path()).unwrap();

    for (expected, query) in [
        // Text comparison a=b is performed using the BINARY collating sequence.
        (vec![1, 2, 3], "SELECT x FROM t1 WHERE a = b;"),
        // Text comparison a=b is performed using the RTRIM collating sequence.
        (
            vec![1, 2, 3, 4],
            "SELECT x FROM t1 WHERE a = b COLLATE RTRIM;",
        ),
        // Text comparison d=a is performed using the NOCASE collating sequence.
        (vec![1, 2, 3, 4], "SELECT x FROM t1 WHERE d = a;"),
        // Text comparison a=d is performed using the BINARY collating sequence.
        (vec![1, 4], "SELECT x FROM t1 WHERE a = d;"),
        // Text comparison 'abc'=c is performed using the RTRIM collating sequence.
        (vec![1, 2, 3], "SELECT x FROM t1 WHERE 'abc' = c;"),
        // Text comparison c='abc' is performed using the RTRIM collating sequence.
        (vec![1, 2, 3], "SELECT x FROM t1 WHERE c = 'abc';"),
        // TODO: Grouping is performed using the NOCASE collating sequence (Values 'abc', 'ABC',
        // and 'Abc' are placed in the same group).
        // (vec![4], "SELECT count(*) FROM t1 GROUP BY d ORDER BY 1;"),
        // TODO: Grouping is performed using the BINARY collating sequence.  'abc' and 'ABC' and
        // 'Abc' form different groups
        // (
        //     vec![1, 1, 2],
        //     "SELECT count(*) FROM t1 GROUP BY (d || '') ORDER BY 1;",
        // ),
        // TODO: Sorting or column c is performed using the RTRIM collating sequence.
        // (vec![4, 1, 2, 3], "SELECT x FROM t1 ORDER BY c, x;"),
        // TODO: Sorting of (c||'') is performed using the BINARY collating sequence.
        // (vec![4, 2, 3, 1], "SELECT x FROM t1 ORDER BY (c||''), x;"),
        // TODO: Sorting of column c is performed using the NOCASE collating sequence.
        // (
        //     vec![2, 4, 3, 1],
        //     "SELECT x FROM t1 ORDER BY c COLLATE NOCASE, x;",
        // ),
    ] {
        let results = load_test_rowids(&test_conn, query);
        assert_eq!(results, expected, "query: {}", query);

        let results = load_rowids(&mut conn, query);
        assert_eq!(results, expected, "query: {}", query);
    }
}

#[test]
fn test_select_preserved_collation_sequence() {
    let file = create_sqlite_database(&[
        "CREATE TABLE t1(x INTEGER PRIMARY KEY, a, b COLLATE BINARY, c COLLATE RTRIM, d COLLATE NOCASE);",
        "INSERT INTO t1 VALUES(1,'abc','abc', 'abc  ','abc');",
        "INSERT INTO t1 VALUES(2,'abc','abc', 'abc',  'ABC');",
        "INSERT INTO t1 VALUES(3,'abc','abc', 'abc ', 'Abc');",
        "INSERT INTO t1 VALUES(4,'abc','abc ','ABC',  'abc');",
        "INSERT INTO t1 VALUES(5,'','a','0 ',  'b');",
        "INSERT INTO t1 VALUES(6,'','a','-1 ',  'b');",
    ]);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    let mut conn = Connection::open(file.path()).unwrap();

    for (expected, query) in [
        // Left collation is prioritized.
        (
            vec![1, 2, 3],
            "SELECT x FROM t1 WHERE a COLLATE BINARY = b COLLATE RTRIM;",
        ),
        // Collation (column) is preserved by CAST.
        (
            vec![1, 2, 3, 4],
            "SELECT x FROM t1 WHERE CAST(d AS TEXT) = CAST(a AS TEXT);",
        ),
        (vec![1, 4], "SELECT x FROM t1 WHERE CAST(a AS TEXT) = d;"),
        // Collation (expression) is preserved by CAST.
        (
            vec![2],
            "SELECT x FROM t1 WHERE CAST(c COLLATE BINARY AS TEXT) = CAST(a COLLATE NOCASE AS TEXT);",
        ),
        (
            vec![2, 4],
            "SELECT x FROM t1 WHERE CAST(a COLLATE NOCASE AS TEXT) = CAST(c COLLATE BINARY AS TEXT);",
        ),
        (
            vec![2, 4],
            "SELECT x FROM t1 WHERE c = CAST(a COLLATE NOCASE AS TEXT);",
        ),
        // Collation (column) is NOT preserved by concatinating.
        (vec![1, 4], "SELECT x FROM t1 WHERE d || 'd' = a || 'd';"),
        (vec![2], "SELECT x FROM t1 WHERE 'a' || c = 'a' || a;"),
        (vec![1, 2, 3, 4], "SELECT x FROM t1 WHERE a || '' = d;"),
        // Collation (column) is NOT preserved by concatinating even if both operand are the same collation.
        (vec![2], "SELECT x FROM t1 WHERE 'ABCABC' = d || d;"),
        // Collation (expression) is preserved by concatinating.
        (vec![1, 2, 3], "SELECT x FROM t1 WHERE 'a' || c = 'a' COLLATE RTRIM || a;"),
        (vec![2, 4], "SELECT x FROM t1 WHERE 'a' COLLATE NOCASE || c = 'a' COLLATE RTRIM || a;"),
        // Collation (column) is NOT preserved by unary -. `-a` is 0 and converted to '0' by right operand
        // CAST.
        (vec![5], "SELECT x FROM t1 WHERE -a = CAST(c AS TEXT);"),
        // Collation (expression) is preserved by unary -.
        (vec![], "SELECT x FROM t1 WHERE -CAST(a COLLATE BINARY AS TEXT) = CAST(c AS TEXT);"),
        // Collation (column) is NOT preserved by unary ~. `-a` is -1 and converted to '-1' by right
        // operand CAST.
        (vec![6], "SELECT x FROM t1 WHERE ~a = CAST(c AS TEXT);"),
        // Collation (expression) is preserved by unary ~.
        (vec![], "SELECT x FROM t1 WHERE ~CAST(a COLLATE BINARY AS TEXT) = CAST(c AS TEXT);"),
        // Collation (column) is NOT preserved by binary operator. `a = 'a'` is 0 and converted to '0' by
        // right operand CAST.
        (vec![5], "SELECT x FROM t1 WHERE a = 'a' = CAST(c AS TEXT);"),
        // Collation (expression) is preserved by binary operator.
        (vec![], "SELECT x FROM t1 WHERE a = 'a' COLLATE BINARY = CAST(c AS TEXT);"),
        (vec![], "SELECT x FROM t1 WHERE a COLLATE BINARY = 'a' COLLATE RTRIM = CAST(c AS TEXT);"),
    ] {
        let results = load_test_rowids(&test_conn, query);
        assert_eq!(results, expected, "query: {}", query);

        let results = load_rowids(&mut conn, query);
        assert_eq!(results, expected, "query: {}", query);
    }
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
    let stmt = conn
        .prepare("SELECT * FROM example WHERE col2 == 5;")
        .unwrap();
    let mut rows = stmt.query().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 3);
    assert_eq!(columns.get(0), &Value::Integer(4));
    assert_eq!(columns.get(1), &Value::Integer(5));
    assert_eq!(columns.get(2), &Value::Integer(6));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());

    let stmt = conn
        .prepare("SELECT col2 FROM example WHERE col2 >= 5;")
        .unwrap();
    let mut rows = stmt.query().unwrap();

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

    let stmt = conn
        .prepare("SELECT col2 FROM example WHERE col2 != 5;")
        .unwrap();
    let mut rows = stmt.query().unwrap();

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
        "CREATE TABLE example(col1, col2, col3, col4);",
        "INSERT INTO example(col1, col2, col3, col4) VALUES ('hello', 2.0, 3, x'01ef');",
        // TODO: col2 = 2 integer?
        "INSERT INTO example(col1, col2, col3, col4) VALUES ('world', 2.0, 9, x'2345ab');",
        "INSERT INTO example(col1, col2, col3, col4) VALUES ('hello', 5.0, 9, x'01ef');",
    ]);

    let mut conn = Connection::open(file.path()).unwrap();
    let stmt = conn
        .prepare("SELECT rowid, col1 FROM example WHERE col1 == 'hello';")
        .unwrap();
    let mut rows = stmt.query().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(1));
    assert_eq!(columns.get(1), &Value::Text(b"hello".as_slice().into()));
    drop(row);

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(3));
    assert_eq!(columns.get(1), &Value::Text(b"hello".as_slice().into()));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());

    let stmt = conn
        .prepare("SELECT rowid, col2 FROM example WHERE col2 = 2.0;")
        .unwrap();
    let mut rows = stmt.query().unwrap();

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

    let stmt = conn
        .prepare("SELECT rowid, col3 FROM example WHERE col3 == 9;")
        .unwrap();
    let mut rows = stmt.query().unwrap();

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

    let stmt = conn
        .prepare("SELECT rowid, col4 FROM example WHERE col4 == x'2345ab';")
        .unwrap();
    let mut rows = stmt.query().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(2));
    assert_eq!(
        columns.get(1),
        &Value::Blob([0x23, 0x45, 0xab].as_slice().into())
    );
    drop(row);

    assert!(rows.next_row().unwrap().is_none());
}

#[test]
fn test_select_filter_ne() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col1, col2, col3, col4);",
        "INSERT INTO example(col1, col2, col3, col4) VALUES ('hello', 2.0, 3, x'01ef');",
        // TODO: col2 = 2 integer?
        "INSERT INTO example(col1, col2, col3, col4) VALUES ('world', 2.0, 9, x'2345ab');",
        "INSERT INTO example(col1, col2, col3, col4) VALUES ('hello', 5.0, 9, x'01ef');",
    ]);

    let mut conn = Connection::open(file.path()).unwrap();
    let stmt = conn
        .prepare("SELECT rowid, col1 FROM example WHERE col1 != 'hello';")
        .unwrap();
    let mut rows = stmt.query().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(2));
    assert_eq!(columns.get(1), &Value::Text(b"world".as_slice().into()));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());

    let stmt = conn
        .prepare("SELECT rowid, col2 FROM example WHERE col2 != 2.0;")
        .unwrap();
    let mut rows = stmt.query().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(3));
    assert_eq!(columns.get(1), &Value::Real(5.0));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());

    let stmt = conn
        .prepare("SELECT rowid, col3 FROM example WHERE col3 != 9;")
        .unwrap();
    let mut rows = stmt.query().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(1));
    assert_eq!(columns.get(1), &Value::Integer(3));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());

    let stmt = conn
        .prepare("SELECT rowid, col4 FROM example WHERE col4 != x'01ef';")
        .unwrap();
    let mut rows = stmt.query().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(2));
    assert_eq!(
        columns.get(1),
        &Value::Blob([0x23, 0x45, 0xab].as_slice().into())
    );
    drop(row);

    assert!(rows.next_row().unwrap().is_none());
}

#[test]
fn test_select_filter_compare() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col);",
        "INSERT INTO example(col) VALUES (null);",
        "INSERT INTO example(col) VALUES (-9223372036854775808);",
        "INSERT INTO example(col) VALUES (-1);",
        "INSERT INTO example(col) VALUES (0);",
        "INSERT INTO example(col) VALUES (1);",
        "INSERT INTO example(col) VALUES (2);",
        "INSERT INTO example(col) VALUES (9223372036854775807);",
        "INSERT INTO example(col) VALUES (-9999999999999999999.0);",
        "INSERT INTO example(col) VALUES (-1.0);",
        "INSERT INTO example(col) VALUES (0.0);",
        "INSERT INTO example(col) VALUES (1.0);",
        "INSERT INTO example(col) VALUES (2.0);",
        "INSERT INTO example(col) VALUES (9999999999999999999.0);",
        "INSERT INTO example(col) VALUES ('hello');",
        "INSERT INTO example(col) VALUES ('');",
        "INSERT INTO example(col) VALUES ('123');",
        "INSERT INTO example(col) VALUES (x'0123456789abcdef');",
        "INSERT INTO example(col) VALUES (x'68656C6C6F');", // 'hello'
        "INSERT INTO example(col) VALUES (x'');",
        "INSERT INTO example(col) VALUES (x'313233');",
    ]);

    let mut conn = Connection::open(file.path()).unwrap();

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();

    for compare_value in [
        "null",
        "-9223372036854775808",
        "-9223372036854775807",
        "-2",
        "-1",
        "0",
        "1",
        "2",
        "3",
        "9223372036854775806",
        "9223372036854775807",
        "9223372036854775808",
        "0.0",
        "0.5",
        "1.0",
        "1.1",
        "2.0",
        "3.0",
        "''",
        "'hello'",
        "'world'",
        "x''",
        "x'0123456789abcdef'",
    ] {
        for op in ["==", "=", "!=", "<", "<=", ">", ">="] {
            let query = format!(
                "SELECT rowid FROM example WHERE col {} {};",
                op, compare_value
            );
            let mut stmt = test_conn.prepare(&query).unwrap();
            let rows = stmt.query([]).unwrap();
            let rowids: Vec<i64> = rows.mapped(|r| r.get(0)).map(|v| v.unwrap()).collect();

            let results = load_rowids(&mut conn, &query);
            assert_eq!(results, rowids, "query: {}", query);
        }
    }
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
    let stmt = conn
        .prepare("SELECT col, RoWid FROM example WHERE rowid = 2;")
        .unwrap();
    let mut rows = stmt.query().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Integer(20));
    assert_eq!(columns.get(1), &Value::Integer(2));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());

    // TODO: Test with rowid = '2'
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

    let stmt = conn
        .prepare("SELECT col, RoWid FROM example WHERE id = 3;")
        .unwrap();
    let mut rows = stmt.query().unwrap();
    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 2);
    assert_eq!(columns.get(0), &Value::Text(b"20".as_slice().into()));
    assert_eq!(columns.get(1), &Value::Integer(3));
    drop(row);
    assert!(rows.next_row().unwrap().is_none());

    let stmt = conn
        .prepare("SELECT col, RoWid FROM example WHERE id = 4;")
        .unwrap();
    let mut rows = stmt.query().unwrap();
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
    let stmt = conn
        .prepare("SELECT * FROM example WHERE col2 == 5;")
        .unwrap();
    let mut rows = stmt.query().unwrap();

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

    let stmt = conn
        .prepare("SELECT * FROM example WHERE col3 == 6;")
        .unwrap();
    let mut rows = stmt.query().unwrap();

    let row = rows.next_row().unwrap().unwrap();
    let columns = row.parse().unwrap();
    assert_eq!(columns.len(), 3);
    assert_eq!(columns.get(0), &Value::Integer(4));
    assert_eq!(columns.get(1), &Value::Integer(5));
    assert_eq!(columns.get(2), &Value::Integer(6));
    drop(row);

    assert!(rows.next_row().unwrap().is_none());

    let stmt = conn
        .prepare("SELECT * FROM example WHERE col3 == 3;")
        .unwrap();
    let mut rows = stmt.query().unwrap();

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

#[test]
fn test_select_with_index_multi_type() {
    let file = create_sqlite_database(&[
        "CREATE TABLE example(col1, col2 INTEGER, col3 TEXT);",
        "CREATE INDEX index1 ON example(col1);",
        "CREATE INDEX index2 ON example(col2);",
        "CREATE INDEX index3 ON example(col3);",
        "INSERT INTO example(col1, col2, col3) VALUES ('abc', 'abc', 'abc');",
        "INSERT INTO example(col1, col2, col3) VALUES ('1234', '1234', '1234');",
        "INSERT INTO example(col1, col2, col3) VALUES (x'31323334', x'31323334', x'31323334');",
        "INSERT INTO example(col1, col2, col3) VALUES (1234, 1234, 1234);",
        "INSERT INTO example(col1, col2, col3) VALUES (1234.5, 1234.5, 1234.5);",
        "INSERT INTO example(col1, col2, col3) VALUES (NULL, NULL, NULL);",
        "INSERT INTO example(col1, col2, col3) VALUES (1234, 1234, 1234);",
        "INSERT INTO example(col1, col2, col3) VALUES ('1234', '1234', '1234');",
        "INSERT INTO example(col1, col2, col3) VALUES ('01234', '01234', '01234');",
    ]);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    let mut conn = Connection::open(file.path()).unwrap();

    for (expected, query) in [
        (vec![4, 7], "col1 = 1234"),
        (vec![2, 4, 7, 8, 9], "col2 = 1234"),
        (vec![2, 4, 7, 8], "col3 = 1234"),
        (vec![], "col1 = 0"),
        (vec![], "col2 = 0"),
        (vec![], "col3 = 0"),
        (vec![2, 8], "col1 = '1234'"),
        (vec![2, 4, 7, 8, 9], "col2 = '1234'"),
        (vec![2, 4, 7, 8], "col3 = '1234'"),
        (vec![9], "col1 = '01234'"),
        (vec![2, 4, 7, 8, 9], "col2 = '01234'"),
        (vec![9], "col3 = '01234'"),
        (vec![], "col1 = '0'"),
        (vec![], "col2 = '0'"),
        (vec![], "col3 = '0'"),
        (vec![5], "col1 = 1234.5"),
        (vec![5], "col2 = 1234.5"),
        (vec![5], "col3 = 1234.5"),
        (vec![3], "col1 = x'31323334'"),
        (vec![3], "col2 = x'31323334'"),
        (vec![3], "col3 = x'31323334'"),
    ] {
        let query = format!("SELECT rowid FROM example WHERE {};", query);
        let mut stmt = test_conn.prepare(&query).unwrap();
        let rows = stmt.query([]).unwrap();
        let rowids: Vec<i64> = rows.mapped(|r| r.get(0)).map(|v| v.unwrap()).collect();
        assert_eq!(rowids, expected, "query: {}", query);

        let results = load_rowids(&mut conn, &query);

        assert_eq!(results, expected, "query: {}", query);
    }
}

#[test]
fn test_select_with_index_same_items() {
    let mut queries = vec![
        "CREATE TABLE example(col1, col2, col3);",
        "CREATE INDEX index1 ON example(col1, col2, col3);",
    ];
    queries.resize(
        queries.len() + 100,
        "INSERT INTO example(col1, col2, col3) VALUES ('abc', NULL, NULL);",
    );
    queries.resize(
        queries.len() + 100,
        "INSERT INTO example(col1, col2, col3) VALUES (123, NULL, NULL);",
    );
    queries.resize(
        queries.len() + 100,
        "INSERT INTO example(col1, col2, col3) VALUES (NULL, NULL, NULL);",
    );
    let file = create_sqlite_database(&queries);

    let test_conn = rusqlite::Connection::open(file.path()).unwrap();
    let mut conn = Connection::open(file.path()).unwrap();

    for (expected, query) in [
        ((1..=100).collect::<Vec<i64>>(), "col1 = 'abc'"),
        ((101..=200).collect::<Vec<i64>>(), "col1 = 123"),
    ] {
        let query = format!("SELECT rowid FROM example WHERE {};", query);
        let mut stmt = test_conn.prepare(&query).unwrap();
        let rows = stmt.query([]).unwrap();
        let rowids: Vec<i64> = rows.mapped(|r| r.get(0)).map(|v| v.unwrap()).collect();
        assert_eq!(rowids, expected, "query: {}", query);

        let results = load_rowids(&mut conn, &query);
        assert_eq!(results, expected, "query: {}", query);
    }
}
