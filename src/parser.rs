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

use crate::record::Value;
use crate::token::get_token_no_space;
use crate::token::Token;
use crate::utils::parse_float_literal;
use crate::utils::parse_integer_literal;
use crate::utils::CaseInsensitiveBytes;
use crate::utils::MaybeQuotedBytes;

pub type Error = &'static str;
pub type Result<T> = std::result::Result<T, Error>;

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
    pub data_type: Option<DataType>,
    pub primary_key: bool,
}

/// Data Type.
///
/// https://www.sqlite.org/datatype3.html
#[derive(Debug, PartialEq, Eq)]
pub enum DataType {
    Null,
    Integer,
    Real,
    Text,
    Blob,
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
        let Some((n, Token::Identifier(name))) = get_token_no_space(input) else {
            return Err("no column name");
        };
        input = &input[n..];

        let (mut n, mut token) = get_token_no_space(input).ok_or("no right paren")?;
        input = &input[n..];
        let data_type = match token {
            Token::Null => {
                (n, token) = get_token_no_space(input).ok_or("no right paren")?;
                input = &input[n..];
                Some(DataType::Null)
            }
            Token::Identifier(data_type) => {
                (n, token) = get_token_no_space(input).ok_or("no right paren")?;
                input = &input[n..];

                // TODO: support affinity parse
                // TODO: compare the performance of UpperToLowerBytes::equal_to_lower_bytes or
                // match + [u8;7]
                let data_type = CaseInsensitiveBytes::from(data_type.raw());
                let data_type = if data_type.equal_to_lower_bytes(b"integer") {
                    DataType::Integer
                } else if data_type.equal_to_lower_bytes(b"real") {
                    DataType::Real
                } else if data_type.equal_to_lower_bytes(b"text") {
                    DataType::Text
                } else if data_type.equal_to_lower_bytes(b"blob") {
                    DataType::Blob
                } else {
                    return Err("unknown data type");
                };
                Some(data_type)
            }
            _ => None,
        };

        let primary_key = if let Token::Primary = token {
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
            data_type,
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
    pub selection: Option<Expr<'a>>,
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

    let selection = if let Some((n, Token::Where)) = get_token_no_space(input) {
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
            selection,
        },
    ))
}

#[derive(Debug, PartialEq, Eq)]
pub enum ResultColumn<'a> {
    All,
    ColumnName(MaybeQuotedBytes<'a>),
}

fn parse_result_column(input: &[u8]) -> Result<(usize, ResultColumn)> {
    match get_token_no_space(input) {
        Some((n, Token::Identifier(id))) => Ok((n, ResultColumn::ColumnName(id))),
        Some((n, Token::Asterisk)) => Ok((n, ResultColumn::All)),
        _ => Err("no result column name"),
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
    BinaryOperator {
        operator: BinaryOperator,
        left: Box<Expr<'a>>,
        right: Box<Expr<'a>>,
    },
    LiteralValue(Value<'a>),
}

fn parse_expr(input: &[u8]) -> Result<(usize, Expr)> {
    let input_len = input.len();
    let (n, left) = match get_token_no_space(input) {
        Some((n, Token::Identifier(id))) => (n, Expr::Column(id)),
        Some((n, Token::Integer(buf))) => {
            let v = parse_integer_literal(buf);
            if v < 0 {
                (n, Expr::LiteralValue(Value::Real(parse_float_literal(buf))))
            } else {
                (n, Expr::LiteralValue(Value::Integer(v)))
            }
        }
        Some((n, Token::Float(buf))) => {
            (n, Expr::LiteralValue(Value::Real(parse_float_literal(buf))))
        }
        _ => return Err("no expr"),
    };
    let input = &input[n..];
    let (n, operator) = match get_token_no_space(input) {
        Some((n, Token::Eq)) => (n, BinaryOperator::Eq),
        Some((n, Token::Ne)) => (n, BinaryOperator::Ne),
        Some((n, Token::Gt)) => (n, BinaryOperator::Gt),
        Some((n, Token::Ge)) => (n, BinaryOperator::Ge),
        Some((n, Token::Lt)) => (n, BinaryOperator::Lt),
        Some((n, Token::Le)) => (n, BinaryOperator::Le),
        _ => return Ok((n, left)),
    };
    let input = &input[n..];

    let (n, right) = parse_expr(input)?;

    Ok((
        input_len - input.len() + n,
        Expr::BinaryOperator {
            operator,
            left: Box::new(left),
            right: Box::new(right),
        },
    ))
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
                    data_type: Some(DataType::Integer),
                    primary_key: true,
                },
                ColumnDef {
                    name: b"name".as_slice().into(),
                    data_type: Some(DataType::Text),
                    primary_key: false,
                },
                ColumnDef {
                    name: b"real".as_slice().into(),
                    data_type: Some(DataType::Real),
                    primary_key: false,
                },
                ColumnDef {
                    name: b"\"blob\"".as_slice().into(),
                    data_type: Some(DataType::Blob),
                    primary_key: false,
                },
                ColumnDef {
                    name: b"`empty`".as_slice().into(),
                    data_type: Some(DataType::Null),
                    primary_key: false,
                },
                ColumnDef {
                    name: b"no_type".as_slice().into(),
                    data_type: None,
                    primary_key: false,
                },
            ]
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
                    data_type: None,
                    primary_key: false,
                },
                ColumnDef {
                    name: b"Name".as_slice().into(),
                    data_type: None,
                    primary_key: false,
                }
            ]
        );
    }

    #[test]
    fn test_parse_create_table_fail() {
        // no right paren.
        assert!(parse_create_table(b"create table foo (id, name ").is_err());
        // invalid data_type.
        assert!(parse_create_table(b"create table foo (id, name invalid)").is_err());
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
        let input = b"select id,name,*,col from foo";
        let (n, select) = parse_select(input).unwrap();
        assert_eq!(n, input.len());
        assert_eq!(select.table_name, b"foo".as_slice().into());
        assert_eq!(
            select.columns,
            vec![
                ResultColumn::ColumnName(b"id".as_slice().into()),
                ResultColumn::ColumnName(b"name".as_slice().into()),
                ResultColumn::All,
                ResultColumn::ColumnName(b"col".as_slice().into())
            ]
        );
    }

    #[test]
    fn test_parse_select_where() {
        let input = b"select * from foo where id = 5";
        let (n, select) = parse_select(input).unwrap();
        assert_eq!(n, input.len());
        assert_eq!(select.table_name, b"foo".as_slice().into());
        assert_eq!(select.columns, vec![ResultColumn::All,]);
        assert!(select.selection.is_some());
        assert_eq!(
            select.selection.unwrap(),
            Expr::BinaryOperator {
                operator: BinaryOperator::Eq,
                left: Box::new(Expr::Column(b"id".as_slice().into())),
                right: Box::new(Expr::LiteralValue(Value::Integer(5))),
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
    fn test_parse_expr() {
        // Parse integer
        assert_eq!(
            parse_expr(b"123456789a").unwrap(),
            (9, Expr::LiteralValue(Value::Integer(123456789)))
        );
        assert_eq!(
            parse_expr(b"00123456789a").unwrap(),
            (11, Expr::LiteralValue(Value::Integer(123456789)))
        );
        assert_eq!(
            parse_expr(b"00000000000000000001a").unwrap(),
            (20, Expr::LiteralValue(Value::Integer(1)))
        );
        assert_eq!(
            parse_expr(b"9223372036854775807").unwrap(),
            (19, Expr::LiteralValue(Value::Integer(9223372036854775807)))
        );
        assert_eq!(
            parse_expr(b"000000000000000000009223372036854775807").unwrap(),
            (39, Expr::LiteralValue(Value::Integer(9223372036854775807)))
        );
        // integer -> float fallback
        assert_eq!(
            parse_expr(b"9223372036854775808").unwrap(),
            (19, Expr::LiteralValue(Value::Real(9223372036854775808.0)))
        );
        assert_eq!(
            parse_expr(b"9999999999999999999").unwrap(),
            (19, Expr::LiteralValue(Value::Real(9999999999999999999.0)))
        );
        assert_eq!(
            parse_expr(b"99999999999999999999a").unwrap(),
            (20, Expr::LiteralValue(Value::Real(99999999999999999999.0)))
        );

        // Parse float
        assert_eq!(
            parse_expr(b".1").unwrap(),
            (2, Expr::LiteralValue(Value::Real(0.1)))
        );
        assert_eq!(
            parse_expr(b"1.").unwrap(),
            (2, Expr::LiteralValue(Value::Real(1.0)))
        );
        assert_eq!(
            parse_expr(b"1.01").unwrap(),
            (4, Expr::LiteralValue(Value::Real(1.01)))
        );
        assert_eq!(
            parse_expr(b"1e1").unwrap(),
            (3, Expr::LiteralValue(Value::Real(10.0)))
        );
        assert_eq!(
            parse_expr(b"1e-1").unwrap(),
            (4, Expr::LiteralValue(Value::Real(0.1)))
        );
    }
}
