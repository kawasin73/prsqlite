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
}
