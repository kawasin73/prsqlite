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

use crate::token::get_token_no_space;
use crate::token::Token;
use crate::utils::parse_float;
use crate::utils::parse_integer;
use crate::utils::HexedBytes;
use crate::utils::MaybeQuotedBytes;
use crate::utils::ParseIntegerResult;

pub type Error = &'static str;
pub type Result<T> = std::result::Result<T, Error>;

static NULL_BYTES: &[u8] = b"null";

/// CREATE TABLE statement.
#[derive(Debug, PartialEq, Eq)]
pub struct CreateTable<'a> {
    pub table_name: MaybeQuotedBytes<'a>,
    pub columns: Vec<ColumnDef<'a>>,
}

/// Definition of a column in a table.
#[derive(Debug, PartialEq, Eq)]
pub struct ColumnDef<'a> {
    pub name: MaybeQuotedBytes<'a>,
    pub type_name: Vec<MaybeQuotedBytes<'a>>,
    pub primary_key: bool,
}

/// https://www.sqlite.org/syntax/signed-number.html
fn skip_signed_number(input: &[u8]) -> Result<usize> {
    let (mut nn, mut token) = get_token_no_space(input).ok_or("no signed number: first token")?;
    let mut n = nn;
    if matches!(token, Token::Plus | Token::Minus) {
        (nn, token) = get_token_no_space(&input[n..]).ok_or("no signed number: number")?;
        n += nn;
    }
    if !matches!(token, Token::Integer(_) | Token::Float(_)) {
        return Err("no signed number is not numeric");
    }
    Ok(n)
}

/// https://www.sqlite.org/syntax/type-name.html
fn parse_type_name(input: &[u8]) -> Result<(usize, Vec<MaybeQuotedBytes<'_>>)> {
    // TODO: Parse type_name to type affinity without converting it to the temporary
    // Vec. Use iterator instead.
    let mut type_name = Vec::new();

    let mut n = match get_token_no_space(input) {
        Some((n, Token::Null)) => {
            type_name.push(NULL_BYTES.into());
            n
        }
        Some((n, Token::Identifier(id))) => {
            type_name.push(id);
            n
        }
        _ => return Ok((0, Vec::new())),
    };

    loop {
        match get_token_no_space(&input[n..]) {
            Some((nn, Token::Null)) => {
                type_name.push(NULL_BYTES.into());
                n += nn;
            }
            Some((nn, Token::Identifier(id))) => {
                type_name.push(id);
                n += nn;
            }
            Some((nn, Token::LeftParen)) => {
                n += nn;
                // Just check whether signed numbers are valid and move cursor without
                // parsing the number. Signed numbers in a type name has no meanings to type
                // affinity.
                // https://www.sqlite.org/datatype3.html#affinity_name_examples
                // Parse signed numbers.
                n += skip_signed_number(&input[n..])?;
                let (mut nn, mut token) =
                    get_token_no_space(&input[n..]).ok_or("no signed number last token")?;
                n += nn;
                if token == Token::Comma {
                    n += skip_signed_number(&input[n..])?;
                    (nn, token) =
                        get_token_no_space(&input[n..]).ok_or("no signed number last token")?;
                    n += nn;
                }
                if token != Token::RightParen {
                    return Err("no right paren");
                }
                break;
            }
            _ => break,
        };
    }

    Ok((n, type_name))
}

/// Parse CREATE TABLE statement.
///
/// https://www.sqlite.org/lang_createtable.html
pub fn parse_create_table(input: &[u8]) -> Result<(usize, CreateTable)> {
    let mut input = input;
    let len_input = input.len();

    let Some((n, Token::Create)) = get_token_no_space(input) else {
        return Err("no create");
    };
    input = &input[n..];

    let Some((n, Token::Table)) = get_token_no_space(input) else {
        return Err("no table");
    };
    input = &input[n..];

    let Some((n, Token::Identifier(table_name))) = get_token_no_space(input) else {
        return Err("no table_name");
    };
    input = &input[n..];

    let Some((n, Token::LeftParen)) = get_token_no_space(input) else {
        return Err("no left paren");
    };
    input = &input[n..];

    let mut columns = Vec::new();
    loop {
        // Parse ColumnDef.
        let Some((n, Token::Identifier(name))) = get_token_no_space(input) else {
            return Err("no column name");
        };
        input = &input[n..];

        let (n, type_name) = parse_type_name(input)?;
        input = &input[n..];

        let (mut n, mut token) = get_token_no_space(input).ok_or("no right paren")?;
        input = &input[n..];

        let primary_key = if token == Token::Primary {
            match get_token_no_space(input) {
                Some((n, Token::Key)) => {
                    input = &input[n..];
                }
                _ => return Err("no key"),
            }
            (n, token) = get_token_no_space(input).ok_or("no right paren")?;
            input = &input[n..];

            true
        } else {
            false
        };

        columns.push(ColumnDef {
            name,
            type_name,
            primary_key,
        });

        match token {
            Token::Comma => continue,
            Token::RightParen => break,
            _ => return Err("no right paren"),
        }
    }

    Ok((
        len_input - input.len(),
        CreateTable {
            table_name,
            columns,
        },
    ))
}

/// CREATE INDEX statement.
#[derive(Debug, PartialEq, Eq)]
pub struct CreateIndex<'a> {
    pub index_name: MaybeQuotedBytes<'a>,
    pub table_name: MaybeQuotedBytes<'a>,
    pub columns: Vec<IndexedColumn<'a>>,
}

/// Definition of a column in a index.
#[derive(Debug, PartialEq, Eq)]
pub struct IndexedColumn<'a> {
    pub name: MaybeQuotedBytes<'a>,
}

/// Parse CREATE INDEX statement.
///
/// https://www.sqlite.org/lang_createindex.html
pub fn parse_create_index(input: &[u8]) -> Result<(usize, CreateIndex)> {
    let mut input = input;
    let len_input = input.len();

    let Some((n, Token::Create)) = get_token_no_space(input) else {
        return Err("no create");
    };
    input = &input[n..];

    let Some((n, Token::Index)) = get_token_no_space(input) else {
        return Err("no index");
    };
    input = &input[n..];

    let Some((n, Token::Identifier(index_name))) = get_token_no_space(input) else {
        return Err("no index_name");
    };
    input = &input[n..];

    let Some((n, Token::On)) = get_token_no_space(input) else {
        return Err("no on");
    };
    input = &input[n..];

    let Some((n, Token::Identifier(table_name))) = get_token_no_space(input) else {
        return Err("no table_name");
    };
    input = &input[n..];

    let Some((n, Token::LeftParen)) = get_token_no_space(input) else {
        return Err("no left paren");
    };
    input = &input[n..];

    let mut columns = Vec::new();
    loop {
        let Some((n, Token::Identifier(name))) = get_token_no_space(input) else {
            return Err("no column name");
        };
        input = &input[n..];

        let (n, token) = get_token_no_space(input).ok_or("no right paren")?;
        input = &input[n..];

        columns.push(IndexedColumn { name });

        match token {
            Token::Comma => continue,
            Token::RightParen => break,
            _ => return Err("no right paren"),
        }
    }

    Ok((
        len_input - input.len(),
        CreateIndex {
            index_name,
            table_name,
            columns,
        },
    ))
}

pub struct Select<'a> {
    pub table_name: MaybeQuotedBytes<'a>,
    pub columns: Vec<ResultColumn<'a>>,
    pub filter: Option<Expr<'a>>,
}

// Parse SELECT statement.
//
// https://www.sqlite.org/lang_select.html
pub fn parse_select(input: &[u8]) -> Result<(usize, Select)> {
    let mut input = input;
    let len_input = input.len();

    let Some((n, Token::Select)) = get_token_no_space(input) else {
        return Err("no select");
    };
    input = &input[n..];

    let (n, result_column) = parse_result_column(input)?;
    input = &input[n..];
    let mut columns = vec![result_column];
    loop {
        match get_token_no_space(input) {
            Some((n, Token::Comma)) => {
                input = &input[n..];
                let (n, result_column) = parse_result_column(input)?;
                input = &input[n..];
                columns.push(result_column);
            }
            Some((n, Token::From)) => {
                input = &input[n..];
                break;
            }
            _ => return Err("no from"),
        }
    }
    let Some((n, Token::Identifier(table_name))) = get_token_no_space(input) else {
        return Err("no table_name");
    };
    input = &input[n..];

    let filter = if let Some((n, Token::Where)) = get_token_no_space(input) {
        input = &input[n..];
        let (n, expr) = parse_expr(input)?;
        input = &input[n..];
        Some(expr)
    } else {
        None
    };

    Ok((
        len_input - input.len(),
        Select {
            table_name,
            columns,
            filter,
        },
    ))
}

#[derive(Debug, PartialEq)]
pub enum ResultColumn<'a> {
    All,
    AllOfTable(MaybeQuotedBytes<'a>),
    Expr((Expr<'a>, Option<MaybeQuotedBytes<'a>>)),
}

/// Parse result column.
///
/// https://www.sqlite.org/syntax/result-column.html
fn parse_result_column(input: &[u8]) -> Result<(usize, ResultColumn)> {
    match get_token_no_space(input) {
        Some((n, Token::Identifier(table_name))) => {
            if let Some((nn, Token::Dot)) = get_token_no_space(&input[n..]) {
                if let Some((nnn, Token::Asterisk)) = get_token_no_space(&input[n + nn..]) {
                    return Ok((n + nn + nnn, ResultColumn::AllOfTable(table_name)));
                }
            }
        }
        Some((n, Token::Asterisk)) => return Ok((n, ResultColumn::All)),
        _ => {}
    }
    let (n, expr) = parse_expr(input)?;
    match get_token_no_space(&input[n..]) {
        Some((nn, Token::Identifier(alias))) => {
            Ok((n + nn, ResultColumn::Expr((expr, Some(alias)))))
        }
        Some((nn, Token::As)) => {
            let Some((nnn, Token::Identifier(alias))) = get_token_no_space(&input[n + nn..]) else {
                return Err("no alias");
            };
            Ok((n + nn + nnn, ResultColumn::Expr((expr, Some(alias)))))
        }
        _ => Ok((n, ResultColumn::Expr((expr, None)))),
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum BinaryOperator {
    /// Equal to
    Eq,
    /// Not equal to
    Ne,
    /// Greater than
    Gt,
    /// Greater than or equal to
    Ge,
    /// Less than
    Lt,
    /// Less than or equal to
    Le,
}

#[derive(Debug, PartialEq)]
pub enum Expr<'a> {
    Column(MaybeQuotedBytes<'a>),
    UnaryMinus(Box<Expr<'a>>),
    BinaryOperator {
        operator: BinaryOperator,
        left: Box<Expr<'a>>,
        right: Box<Expr<'a>>,
    },
    Cast {
        expr: Box<Expr<'a>>,
        type_name: Vec<MaybeQuotedBytes<'a>>,
    },
    Null,
    Integer(i64),
    Real(f64),
    Text(MaybeQuotedBytes<'a>),
    Blob(HexedBytes<'a>),
}

/// Parse expression.
///
/// https://www.sqlite.org/syntax/expr.html
fn parse_expr(input: &[u8]) -> Result<(usize, Expr)> {
    let Some((n, token)) = get_token_no_space(input) else {
        return Err("no expr");
    };
    let (nn, expr) = parse_expr_eq(token, &input[n..])?;
    Ok((n + nn, expr))
}

fn parse_expr_eq<'a>(token: Token<'a>, input: &'a [u8]) -> Result<(usize, Expr<'a>)> {
    let (mut n, mut expr) = parse_expr_compare(token, input)?;
    loop {
        let (nn, operator) = match get_token_no_space(&input[n..]) {
            Some((n, Token::Eq)) => (n, BinaryOperator::Eq),
            Some((n, Token::Ne)) => (n, BinaryOperator::Ne),
            _ => break,
        };
        n += nn;
        let Some((nn, token)) = get_token_no_space(&input[n..]) else {
            return Err("no expr after eq/ne");
        };
        n += nn;
        let (nn, right) = parse_expr_compare(token, &input[n..])?;
        n += nn;
        expr = Expr::BinaryOperator {
            operator,
            left: Box::new(expr),
            right: Box::new(right),
        };
    }
    Ok((n, expr))
}

fn parse_expr_compare<'a>(token: Token<'a>, input: &'a [u8]) -> Result<(usize, Expr<'a>)> {
    let (mut n, mut expr) = parse_expr_unary(token, input)?;
    loop {
        let (nn, operator) = match get_token_no_space(&input[n..]) {
            Some((n, Token::Gt)) => (n, BinaryOperator::Gt),
            Some((n, Token::Ge)) => (n, BinaryOperator::Ge),
            Some((n, Token::Lt)) => (n, BinaryOperator::Lt),
            Some((n, Token::Le)) => (n, BinaryOperator::Le),
            _ => break,
        };
        n += nn;
        let Some((nn, token)) = get_token_no_space(&input[n..]) else {
            return Err("no expr after eq/ne");
        };
        n += nn;
        let (nn, right) = parse_expr_unary(token, &input[n..])?;
        n += nn;
        expr = Expr::BinaryOperator {
            operator,
            left: Box::new(expr),
            right: Box::new(right),
        };
    }
    Ok((n, expr))
}

fn parse_expr_unary<'a>(token: Token<'a>, input: &'a [u8]) -> Result<(usize, Expr<'a>)> {
    match token {
        Token::Plus => {
            let Some((n, token)) = get_token_no_space(input) else {
                return Err("no expr after +");
            };
            // Unary operator + is a no-op.
            let (nn, expr) = parse_expr_unary(token, &input[n..])?;
            Ok((n + nn, expr))
        }
        Token::Minus => match get_token_no_space(input) {
            Some((n, Token::Integer(buf))) => {
                let (valid, parsed_int) = parse_integer(buf);
                assert!(valid);
                match parsed_int {
                    ParseIntegerResult::Integer(v) => Ok((n, Expr::Integer(-v))),
                    ParseIntegerResult::MaxPlusOne => Ok((n, Expr::Integer(i64::MIN))),
                    ParseIntegerResult::TooBig(_) => {
                        let (valid, pure_integer, d) = parse_float(buf);
                        assert!(valid);
                        assert!(pure_integer);
                        Ok((n, Expr::Real(-d)))
                    }
                    ParseIntegerResult::Empty => {
                        unreachable!("token integer must contain at least 1 digits only")
                    }
                }
            }
            Some((n, Token::Float(buf))) => {
                let (valid, pure_integer, d) = parse_float(buf);
                assert!(valid);
                assert!(!pure_integer);
                Ok((n, Expr::Real(-d)))
            }
            Some((n, token)) => {
                let (nn, expr) = parse_expr_unary(token, &input[n..])?;
                Ok((n + nn, Expr::UnaryMinus(Box::new(expr))))
            }
            _ => Err("no expr"),
        },
        _ => parse_expr_primitive(token, input),
    }
}

fn parse_expr_primitive<'a>(token: Token<'a>, input: &'a [u8]) -> Result<(usize, Expr<'a>)> {
    match token {
        Token::Identifier(id) => Ok((0, Expr::Column(id))),
        Token::Cast => {
            let Some((mut n, Token::LeftParen)) = get_token_no_space(input) else {
                return Err("no cast left paren");
            };

            let (nn, expr) = parse_expr(&input[n..])?;
            n += nn;

            let Some((nn, Token::As)) = get_token_no_space(&input[n..]) else {
                return Err("no cast as");
            };
            n += nn;

            let (nn, type_name) = parse_type_name(&input[n..])?;
            n += nn;

            let Some((nn, Token::RightParen)) = get_token_no_space(&input[n..]) else {
                return Err("no cast right paren");
            };
            n += nn;

            Ok((
                n,
                Expr::Cast {
                    expr: Box::new(expr),
                    type_name,
                },
            ))
        }
        Token::Null => Ok((0, Expr::Null)),
        Token::Integer(buf) => {
            let (valid, parsed_int) = parse_integer(buf);
            assert!(valid);
            match parsed_int {
                ParseIntegerResult::Integer(v) => Ok((0, Expr::Integer(v))),
                ParseIntegerResult::MaxPlusOne | ParseIntegerResult::TooBig(_) => {
                    let (valid, pure_integer, d) = parse_float(buf);
                    assert!(valid);
                    assert!(pure_integer);
                    Ok((0, Expr::Real(d)))
                }
                ParseIntegerResult::Empty => {
                    unreachable!("token integer must contain at least 1 digits only")
                }
            }
        }
        Token::Float(buf) => {
            let (valid, pure_integer, d) = parse_float(buf);
            assert!(valid);
            assert!(!pure_integer);
            Ok((0, Expr::Real(d)))
        }
        Token::String(text) => Ok((0, Expr::Text(text))),
        Token::Blob(hex) => Ok((0, Expr::Blob(hex))),
        _ => Err("no expr"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_create_table() {
        let input = b"create table foo (id integer primary key, name text, real real, \"blob\" blob, `empty` null,[no_type])";
        let (n, create_table) = parse_create_table(input).unwrap();
        assert_eq!(n, input.len());
        assert_eq!(create_table.table_name, b"foo".as_slice().into());
        assert_eq!(
            create_table.columns,
            vec![
                ColumnDef {
                    name: b"id".as_slice().into(),
                    type_name: vec![b"integer".as_slice().into()],
                    primary_key: true,
                },
                ColumnDef {
                    name: b"name".as_slice().into(),
                    type_name: vec![b"text".as_slice().into()],
                    primary_key: false,
                },
                ColumnDef {
                    name: b"real".as_slice().into(),
                    type_name: vec![b"real".as_slice().into()],
                    primary_key: false,
                },
                ColumnDef {
                    name: b"\"blob\"".as_slice().into(),
                    type_name: vec![b"blob".as_slice().into()],
                    primary_key: false,
                },
                ColumnDef {
                    name: b"`empty`".as_slice().into(),
                    type_name: vec![b"null".as_slice().into()],
                    primary_key: false,
                },
                ColumnDef {
                    name: b"no_type".as_slice().into(),
                    type_name: vec![],
                    primary_key: false,
                },
            ]
        );
    }
    #[test]
    fn test_parse_create_table_type_name() {
        let input = b"create table foo (col1 type type primary key, col2 Varint(10), col3 [Float](+10), col4 \"test\"(-10.0), col5 null(0), col6 `blob```(1,+2))";
        let (n, create_table) = parse_create_table(input).unwrap();
        assert_eq!(n, input.len());
        assert_eq!(create_table.table_name, b"foo".as_slice().into());
        assert_eq!(create_table.columns.len(), 6);
        assert_eq!(
            create_table.columns[0].type_name,
            vec![b"type".as_slice().into(), b"type".as_slice().into()]
        );
        assert_eq!(
            create_table.columns[1].type_name,
            vec![b"Varint".as_slice().into()]
        );
        assert_eq!(
            create_table.columns[2].type_name,
            vec![b"Float".as_slice().into()]
        );
        assert_eq!(
            create_table.columns[3].type_name,
            vec![b"\"test\"".as_slice().into()]
        );
        assert_eq!(
            create_table.columns[4].type_name,
            vec![b"null".as_slice().into()]
        );
        assert_eq!(
            create_table.columns[5].type_name,
            vec![b"`blob```".as_slice().into()]
        );
    }

    #[test]
    fn test_parse_create_table_with_extra() {
        let input = b"create table Foo (Id, Name)abc ";
        let (n, create_table) = parse_create_table(input).unwrap();
        assert_eq!(n, input.len() - 4);
        assert_eq!(create_table.table_name, b"Foo".as_slice().into());
        assert_eq!(
            create_table.columns,
            vec![
                ColumnDef {
                    name: b"Id".as_slice().into(),
                    type_name: Vec::new(),
                    primary_key: false,
                },
                ColumnDef {
                    name: b"Name".as_slice().into(),
                    type_name: Vec::new(),
                    primary_key: false,
                }
            ]
        );
    }

    #[test]
    fn test_parse_create_table_fail() {
        // no right paren.
        assert!(parse_create_table(b"create table foo (id, name ").is_err());
        // primary without key.
        assert!(parse_create_table(b"create table foo (id primary, name)").is_err());
        // key without primary.
        assert!(parse_create_table(b"create table foo (id key, name)").is_err());
    }

    #[test]
    fn test_parse_create_index() {
        let input = b"create index foo on bar (col1, col2,col3)";
        let (n, create_index) = parse_create_index(input).unwrap();
        assert_eq!(n, input.len());
        assert_eq!(create_index.index_name, b"foo".as_slice().into());
        assert_eq!(create_index.table_name, b"bar".as_slice().into());
        assert_eq!(
            create_index.columns,
            vec![
                IndexedColumn {
                    name: b"col1".as_slice().into()
                },
                IndexedColumn {
                    name: b"col2".as_slice().into()
                },
                IndexedColumn {
                    name: b"col3".as_slice().into()
                },
            ]
        );
    }

    #[test]
    fn test_parse_create_index_with_extra() {
        let input = b"create index fOo on bAR (Col1,cOL2)abc ";
        let (n, create_index) = parse_create_index(input).unwrap();
        assert_eq!(n, input.len() - 4);
        assert_eq!(create_index.index_name, b"fOo".as_slice().into());
        assert_eq!(create_index.table_name, b"bAR".as_slice().into());
        assert_eq!(
            create_index.columns,
            vec![
                IndexedColumn {
                    name: b"Col1".as_slice().into()
                },
                IndexedColumn {
                    name: b"cOL2".as_slice().into()
                },
            ]
        );
    }

    #[test]
    fn test_parse_create_index_fail() {
        // no right paren.
        assert!(parse_create_index(b"create index foo on bar (id, name ").is_err());
    }

    #[test]
    fn test_parse_select_all() {
        let input = b"select * from foo";
        let (n, select) = parse_select(input).unwrap();
        assert_eq!(n, input.len());
        assert_eq!(select.table_name, b"foo".as_slice().into());
        assert_eq!(select.columns, vec![ResultColumn::All]);
    }

    #[test]
    fn test_parse_select_columns() {
        let input = b"select id,name,*,col as col2, col3 col4, 10, 'text' as col5, col = 11, col2 < col3 as col6 from foo";
        let (n, select) = parse_select(input).unwrap();
        assert_eq!(n, input.len());
        assert_eq!(select.table_name, b"foo".as_slice().into());
        assert_eq!(
            select.columns,
            vec![
                ResultColumn::Expr((Expr::Column(b"id".as_slice().into()), None)),
                ResultColumn::Expr((Expr::Column(b"name".as_slice().into()), None)),
                ResultColumn::All,
                ResultColumn::Expr((
                    Expr::Column(b"col".as_slice().into()),
                    Some(b"col2".as_slice().into())
                )),
                ResultColumn::Expr((
                    Expr::Column(b"col3".as_slice().into()),
                    Some(b"col4".as_slice().into())
                )),
                ResultColumn::Expr((Expr::Integer(10), None)),
                ResultColumn::Expr((
                    Expr::Text(b"'text'".as_slice().into()),
                    Some(b"col5".as_slice().into())
                )),
                ResultColumn::Expr((
                    Expr::BinaryOperator {
                        operator: BinaryOperator::Eq,
                        left: Box::new(Expr::Column(b"col".as_slice().into())),
                        right: Box::new(Expr::Integer(11)),
                    },
                    None
                )),
                ResultColumn::Expr((
                    Expr::BinaryOperator {
                        operator: BinaryOperator::Lt,
                        left: Box::new(Expr::Column(b"col2".as_slice().into())),
                        right: Box::new(Expr::Column(b"col3".as_slice().into())),
                    },
                    Some(b"col6".as_slice().into())
                ))
            ]
        );
    }

    #[test]
    fn test_parse_select_table_all() {
        let input = b"select bar.* from foo";
        let (n, select) = parse_select(input).unwrap();
        assert_eq!(n, input.len());
        assert_eq!(select.table_name, b"foo".as_slice().into());
        assert_eq!(
            select.columns,
            vec![ResultColumn::AllOfTable(b"bar".as_slice().into()),]
        );
    }

    #[test]
    fn test_parse_select_where() {
        let input = b"select * from foo where id = 5";
        let (n, select) = parse_select(input).unwrap();
        assert_eq!(n, input.len());
        assert_eq!(select.table_name, b"foo".as_slice().into());
        assert_eq!(select.columns, vec![ResultColumn::All,]);
        assert!(select.filter.is_some());
        assert_eq!(
            select.filter.unwrap(),
            Expr::BinaryOperator {
                operator: BinaryOperator::Eq,
                left: Box::new(Expr::Column(b"id".as_slice().into())),
                right: Box::new(Expr::Integer(5)),
            }
        );
    }

    #[test]
    fn test_parse_select_fail() {
        // no table name.
        let input = b"select col from ";
        assert!(parse_create_table(input).is_err());
    }

    #[test]
    fn test_parse_expr_literal_value() {
        // Parse null
        assert_eq!(parse_expr(b"null").unwrap(), (4, Expr::Null));

        // Parse integer
        assert_eq!(
            parse_expr(b"123456789a").unwrap(),
            (9, Expr::Integer(123456789))
        );
        assert_eq!(
            parse_expr(b"00123456789a").unwrap(),
            (11, Expr::Integer(123456789))
        );
        assert_eq!(
            parse_expr(b"00000000000000000001a").unwrap(),
            (20, Expr::Integer(1))
        );
        assert_eq!(
            parse_expr(b"9223372036854775807").unwrap(),
            (19, Expr::Integer(9223372036854775807))
        );
        assert_eq!(
            parse_expr(b"000000000000000000009223372036854775807").unwrap(),
            (39, Expr::Integer(9223372036854775807))
        );
        // integer -> float fallback
        assert_eq!(
            parse_expr(b"9223372036854775808").unwrap(),
            (19, Expr::Real(9223372036854775808.0))
        );
        assert_eq!(
            parse_expr(b"9999999999999999999").unwrap(),
            (19, Expr::Real(9999999999999999999.0))
        );
        assert_eq!(
            parse_expr(b"99999999999999999999a").unwrap(),
            (20, Expr::Real(99999999999999999999.0))
        );

        // Parse float
        assert_eq!(parse_expr(b".1").unwrap(), (2, Expr::Real(0.1)));
        assert_eq!(parse_expr(b"1.").unwrap(), (2, Expr::Real(1.0)));
        assert_eq!(parse_expr(b"1.01").unwrap(), (4, Expr::Real(1.01)));
        assert_eq!(parse_expr(b"1e1").unwrap(), (3, Expr::Real(10.0)));
        assert_eq!(parse_expr(b"1e-1").unwrap(), (4, Expr::Real(0.1)));

        // Parse string
        assert_eq!(
            parse_expr(b"'hello'").unwrap(),
            (7, Expr::Text(b"'hello'".as_slice().into()))
        );
        assert_eq!(
            parse_expr(b"'hel''lo'").unwrap(),
            (9, Expr::Text(b"'hel''lo'".as_slice().into()))
        );

        // Parse blob
        assert_eq!(
            parse_expr(b"x'0123456789abcdef' ").unwrap(),
            (19, Expr::Blob(b"0123456789abcdef".as_slice().into()))
        );
        assert_eq!(
            parse_expr(b"X'0123456789abcdef' ").unwrap(),
            (19, Expr::Blob(b"0123456789abcdef".as_slice().into()))
        );
    }

    #[test]
    fn test_parse_expr_column() {
        assert_eq!(
            parse_expr(b"foo").unwrap(),
            (3, Expr::Column(b"foo".as_slice().into()))
        );
        assert_eq!(
            parse_expr(b"\"foo\"").unwrap(),
            (5, Expr::Column(b"\"foo\"".as_slice().into()))
        );
    }

    #[test]
    fn test_parse_expr_cast() {
        assert_eq!(
            parse_expr(b"cast(100as text) ").unwrap(),
            (
                16,
                Expr::Cast {
                    expr: Box::new(Expr::Integer(100)),
                    type_name: vec![b"text".as_slice().into()],
                }
            )
        );
        assert_eq!(
            parse_expr(b"cast ( '100' as integer) ").unwrap(),
            (
                24,
                Expr::Cast {
                    expr: Box::new(Expr::Text(b"'100'".as_slice().into())),
                    type_name: vec![b"integer".as_slice().into()],
                }
            )
        );
        assert_eq!(
            parse_expr(b"cast (col = 100 as integer) ").unwrap(),
            (
                27,
                Expr::Cast {
                    expr: Box::new(Expr::BinaryOperator {
                        operator: BinaryOperator::Eq,
                        left: Box::new(Expr::Column(b"col".as_slice().into())),
                        right: Box::new(Expr::Integer(100))
                    }),
                    type_name: vec![b"integer".as_slice().into()],
                }
            )
        );
    }

    #[test]
    fn test_parse_expr_unary_operator() {
        assert_eq!(
            parse_expr(b"+foo").unwrap(),
            (4, Expr::Column(b"foo".as_slice().into()))
        );
        assert_eq!(
            parse_expr(b"-foo").unwrap(),
            (
                4,
                Expr::UnaryMinus(Box::new(Expr::Column(b"foo".as_slice().into())))
            )
        );
        assert_eq!(
            parse_expr(b"-+-+-foo").unwrap(),
            (
                8,
                Expr::UnaryMinus(Box::new(Expr::UnaryMinus(Box::new(Expr::UnaryMinus(
                    Box::new(Expr::Column(b"foo".as_slice().into()))
                )))))
            )
        );
        assert_eq!(parse_expr(b"+123").unwrap(), (4, Expr::Integer(123)));
        assert_eq!(parse_expr(b"+ 123").unwrap(), (5, Expr::Integer(123)));
        assert_eq!(parse_expr(b"-123").unwrap(), (4, Expr::Integer(-123)));
        assert_eq!(parse_expr(b"- 123").unwrap(), (5, Expr::Integer(-123)));
        assert_eq!(
            parse_expr(b"-9223372036854775808").unwrap(),
            (20, Expr::Integer(-9223372036854775808))
        );
        assert_eq!(
            parse_expr(b"-+-123").unwrap(),
            (6, Expr::UnaryMinus(Box::new(Expr::Integer(-123))))
        );
        assert_eq!(parse_expr(b"+123.4").unwrap(), (6, Expr::Real(123.4)));
        assert_eq!(parse_expr(b"-123.4").unwrap(), (6, Expr::Real(-123.4)));
        assert_eq!(
            parse_expr(b"-+-123.4").unwrap(),
            (8, Expr::UnaryMinus(Box::new(Expr::Real(-123.4))))
        );
        assert_eq!(
            parse_expr(b"+'abc'").unwrap(),
            (6, Expr::Text(b"'abc'".as_slice().into()))
        );
        assert_eq!(
            parse_expr(b"-'abc'").unwrap(),
            (
                6,
                Expr::UnaryMinus(Box::new(Expr::Text(b"'abc'".as_slice().into())))
            )
        );
        assert_eq!(
            parse_expr(b"-abc").unwrap(),
            (
                4,
                Expr::UnaryMinus(Box::new(Expr::Column(b"abc".as_slice().into())))
            )
        );
    }

    #[test]
    fn test_parse_expr_compare() {
        assert_eq!(
            parse_expr(b"-1 < 2").unwrap(),
            (
                6,
                Expr::BinaryOperator {
                    operator: BinaryOperator::Lt,
                    left: Box::new(Expr::Integer(-1)),
                    right: Box::new(Expr::Integer(2)),
                }
            )
        );
        assert_eq!(
            parse_expr(b"-1 <= 2").unwrap(),
            (
                7,
                Expr::BinaryOperator {
                    operator: BinaryOperator::Le,
                    left: Box::new(Expr::Integer(-1)),
                    right: Box::new(Expr::Integer(2)),
                }
            )
        );
        assert_eq!(
            parse_expr(b"-1 > 2").unwrap(),
            (
                6,
                Expr::BinaryOperator {
                    operator: BinaryOperator::Gt,
                    left: Box::new(Expr::Integer(-1)),
                    right: Box::new(Expr::Integer(2)),
                }
            )
        );
        assert_eq!(
            parse_expr(b"-1 >= 2").unwrap(),
            (
                7,
                Expr::BinaryOperator {
                    operator: BinaryOperator::Ge,
                    left: Box::new(Expr::Integer(-1)),
                    right: Box::new(Expr::Integer(2)),
                }
            )
        );
        assert_eq!(
            parse_expr(b"-1 >= 2 >= -abc").unwrap(),
            (
                15,
                Expr::BinaryOperator {
                    operator: BinaryOperator::Ge,
                    left: Box::new(Expr::BinaryOperator {
                        operator: BinaryOperator::Ge,
                        left: Box::new(Expr::Integer(-1)),
                        right: Box::new(Expr::Integer(2)),
                    }),
                    right: Box::new(Expr::UnaryMinus(Box::new(Expr::Column(
                        b"abc".as_slice().into()
                    )))),
                }
            )
        );
    }

    #[test]
    fn test_parse_expr_eq() {
        assert_eq!(
            parse_expr(b"-1 = 2").unwrap(),
            (
                6,
                Expr::BinaryOperator {
                    operator: BinaryOperator::Eq,
                    left: Box::new(Expr::Integer(-1)),
                    right: Box::new(Expr::Integer(2)),
                }
            )
        );
        assert_eq!(
            parse_expr(b"-1 == 2").unwrap(),
            (
                7,
                Expr::BinaryOperator {
                    operator: BinaryOperator::Eq,
                    left: Box::new(Expr::Integer(-1)),
                    right: Box::new(Expr::Integer(2)),
                }
            )
        );
        assert_eq!(
            parse_expr(b"-1 != 2").unwrap(),
            (
                7,
                Expr::BinaryOperator {
                    operator: BinaryOperator::Ne,
                    left: Box::new(Expr::Integer(-1)),
                    right: Box::new(Expr::Integer(2)),
                }
            )
        );
        assert_eq!(
            parse_expr(b"-1 <> 2").unwrap(),
            (
                7,
                Expr::BinaryOperator {
                    operator: BinaryOperator::Ne,
                    left: Box::new(Expr::Integer(-1)),
                    right: Box::new(Expr::Integer(2)),
                }
            )
        );
        assert_eq!(
            parse_expr(b"1 = 2 = 3").unwrap(),
            (
                9,
                Expr::BinaryOperator {
                    operator: BinaryOperator::Eq,
                    left: Box::new(Expr::BinaryOperator {
                        operator: BinaryOperator::Eq,
                        left: Box::new(Expr::Integer(1)),
                        right: Box::new(Expr::Integer(2)),
                    }),
                    right: Box::new(Expr::Integer(3)),
                }
            )
        );
        assert_eq!(
            parse_expr(b"1 < 2 = 3 < 4").unwrap(),
            (
                13,
                Expr::BinaryOperator {
                    operator: BinaryOperator::Eq,
                    left: Box::new(Expr::BinaryOperator {
                        operator: BinaryOperator::Lt,
                        left: Box::new(Expr::Integer(1)),
                        right: Box::new(Expr::Integer(2)),
                    }),
                    right: Box::new(Expr::BinaryOperator {
                        operator: BinaryOperator::Lt,
                        left: Box::new(Expr::Integer(3)),
                        right: Box::new(Expr::Integer(4)),
                    }),
                }
            )
        );
        assert_eq!(
            parse_expr(b"1 < 2 = 3 < 4 = 5").unwrap(),
            (
                17,
                Expr::BinaryOperator {
                    operator: BinaryOperator::Eq,
                    left: Box::new(Expr::BinaryOperator {
                        operator: BinaryOperator::Eq,
                        left: Box::new(Expr::BinaryOperator {
                            operator: BinaryOperator::Lt,
                            left: Box::new(Expr::Integer(1)),
                            right: Box::new(Expr::Integer(2)),
                        }),
                        right: Box::new(Expr::BinaryOperator {
                            operator: BinaryOperator::Lt,
                            left: Box::new(Expr::Integer(3)),
                            right: Box::new(Expr::Integer(4)),
                        }),
                    }),
                    right: Box::new(Expr::Integer(5)),
                }
            )
        );
    }
}
