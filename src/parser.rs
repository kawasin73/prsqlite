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

pub type Error = &'static str;
pub type Result<T> = std::result::Result<T, Error>;

pub struct CreateTable<'a> {
    pub table_name: &'a [u8],
    pub columns: Vec<&'a [u8]>,
}

/// Parse CREATE TABLE statement.
///
/// https://www.sqlite.org/lang_createtable.html
pub fn parse_create_table(input: &[u8]) -> Result<(usize, CreateTable)> {
    let mut input = input;
    let len_input = input.len();

    if let Some((n, Token::Create)) = get_token_no_space(input) {
        input = &input[n..];
    } else {
        return Err("no create");
    }
    if let Some((n, Token::Table)) = get_token_no_space(input) {
        input = &input[n..];
    } else {
        return Err("no table");
    }
    let table_name = if let Some((n, Token::Identifier(table_name))) = get_token_no_space(input) {
        input = &input[n..];
        table_name
    } else {
        return Err("no table_name");
    };
    if let Some((n, Token::LeftParen)) = get_token_no_space(input) {
        input = &input[n..];
    } else {
        return Err("no left paren");
    }
    let mut columns = Vec::new();
    loop {
        if let Some((n, Token::Identifier(column_name))) = get_token_no_space(input) {
            input = &input[n..];
            columns.push(column_name);
        } else {
            return Err("no column name");
        }
        match get_token_no_space(input) {
            Some((n, Token::Comma)) => {
                input = &input[n..];
            }
            Some((n, Token::RightParen)) => {
                input = &input[n..];
                break;
            }
            _ => return Err("no right paren"),
        }
    }
    Ok((len_input - input.len(), CreateTable { table_name, columns }))
}

pub struct Select<'a> {
    pub table_name: &'a [u8],
    pub columns: Vec<ResultColumn<'a>>,
}

// Parse SELECT statement.
//
// https://www.sqlite.org/lang_select.html
pub fn parse_select(input: &[u8]) -> Result<(usize, Select)> {
    let mut input = input;
    let len_input = input.len();

    if let Some((n, Token::Select)) = get_token_no_space(input) {
        input = &input[n..];
    } else {
        return Err("no select");
    }
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
    let table_name = if let Some((n, Token::Identifier(table_name))) = get_token_no_space(input) {
        input = &input[n..];
        table_name
    } else {
        return Err("no table_name");
    };

    Ok((len_input - input.len(), Select { table_name, columns }))
}

#[derive(Debug, PartialEq, Eq)]
pub enum ResultColumn<'a> {
    All,
    ColumnName(&'a [u8]),
}

fn parse_result_column(input: &[u8]) -> Result<(usize, ResultColumn)> {
    match get_token_no_space(input) {
        Some((n, Token::Identifier(id))) => Ok((n, ResultColumn::ColumnName(id))),
        Some((n, Token::Asterisk)) => Ok((n, ResultColumn::All)),
        _ => Err("no result column name"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_create_table() {
        let input = b"create table foo (id, name)";
        let (n, create_table) = parse_create_table(input).unwrap();
        assert_eq!(n, input.len());
        assert_eq!(create_table.table_name, b"foo");
        let expected_columns: Vec<&[u8]> = vec![b"id", b"name"];
        assert_eq!(create_table.columns, expected_columns);
    }

    #[test]
    fn test_parse_create_table_with_extra() {
        let input = b"create table Foo (Id, Name)abc ";
        let (n, create_table) = parse_create_table(input).unwrap();
        assert_eq!(n, input.len() - 4);
        assert_eq!(create_table.table_name, b"Foo");
        let expected_columns: Vec<&[u8]> = vec![b"Id", b"Name"];
        assert_eq!(create_table.columns, expected_columns);
    }

    #[test]
    fn test_parse_create_table_fail() {
        // no right paren.
        let input = b"create table foo (id, name ";
        assert!(parse_create_table(input).is_err());
    }

    #[test]
    fn test_parse_select_all() {
        let input = b"select * from foo";
        let (n, select) = parse_select(input).unwrap();
        assert_eq!(n, input.len());
        assert_eq!(select.table_name, b"foo");
        assert_eq!(select.columns, vec![ResultColumn::All]);
    }

    #[test]
    fn test_parse_select_columns() {
        let input = b"select id,name,*,col from foo";
        let (n, select) = parse_select(input).unwrap();
        assert_eq!(n, input.len());
        assert_eq!(select.table_name, b"foo");
        assert_eq!(
            select.columns,
            vec![
                ResultColumn::ColumnName(b"id"),
                ResultColumn::ColumnName(b"name"),
                ResultColumn::All,
                ResultColumn::ColumnName(b"col")
            ]
        );
    }

    #[test]
    fn test_parse_select_fail() {
        // no table name.
        let input = b"select col from ";
        assert!(parse_create_table(input).is_err());
    }
}
