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

use crate::utils::UPPER_TO_LOWER;

const CHAR_ALPHABET: u8 = 0x01;
const CHAR_UNDERSCORE: u8 = 0x02;
const CHAR_DIGIT: u8 = 0x03;
const CHAR_INVALID: u8 = 0xFF;

static CHAR_LOOKUP_TABLE: [u8; 256] = [
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, b' ', b' ', 0xFF, b' ', b' ', 0xFF, 0xFF, 0xFF, // 0x00 - 0x0F
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0x10 - 0x1F
    b' ', b'!', 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, b'(', b')', b'*', 0xFF, b',', 0xFF, 0xFF, 0xFF, // 0x20 - 0x2F
    0x03, 0x03, 0x03, 0x03, 0x03, 0x03, 0x03, 0x03, 0x03, 0x03, 0xFF, b';', b'<', b'=', b'>', 0xFF, // 0x30 - 0x3F
    0xFF, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, // 0x40 - 0x4F
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0xFF, 0xFF, 0xFF, 0xFF, 0x02, // 0x50 - 0x5F
    0xFF, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, // 0x60 - 0x6F
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0x70 - 0x7F
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0x80 - 0x8F
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0x90 - 0x9F
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xA0 - 0xAF
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xB0 - 0xBF
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xC0 - 0xCF
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xD0 - 0xDF
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xE0 - 0xEF
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xF0 - 0xFF
];

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Token<'a> {
    Select,
    From,
    Where,
    Create,
    Table,
    Index,
    Primary,
    Key,
    On,
    Null,
    Space,
    LeftParen,
    RightParen,
    Asterisk,
    Comma,
    Semicolon,
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
    Identifier(&'a [u8]),
    Integer(i64),
    Illegal,
}

pub fn get_token_no_space(input: &[u8]) -> Option<(usize, Token)> {
    match get_token(input) {
        Some((len_space, Token::Space)) => {
            let (len, token) = get_token(&input[len_space..])?;
            Some((len + len_space, token))
        }
        result => result,
    }
}

pub fn get_token(input: &[u8]) -> Option<(usize, Token)> {
    if input.is_empty() {
        return None;
    }
    match CHAR_LOOKUP_TABLE[input[0] as usize] {
        b' ' => {
            for (i, &byte) in input.iter().skip(1).enumerate() {
                if byte != b' ' {
                    return Some((i + 1, Token::Space));
                }
            }
            Some((input.len(), Token::Space))
        }
        b'!' => {
            if input.len() >= 2 && input[1] == b'=' {
                Some((2, Token::Ne))
            } else {
                Some((1, Token::Illegal))
            }
        }
        b'(' => Some((1, Token::LeftParen)),
        b')' => Some((1, Token::RightParen)),
        b'*' => Some((1, Token::Asterisk)),
        b',' => Some((1, Token::Comma)),
        b';' => Some((1, Token::Semicolon)),
        b'<' => {
            if input.len() >= 2 {
                match input[1] {
                    b'=' => Some((2, Token::Le)),
                    b'>' => Some((2, Token::Ne)),
                    _ => Some((1, Token::Lt)),
                }
            } else {
                Some((1, Token::Lt))
            }
        }
        b'=' => {
            if input.len() >= 2 && input[1] == b'=' {
                Some((2, Token::Eq))
            } else {
                Some((1, Token::Eq))
            }
        }
        b'>' => {
            if input.len() >= 2 && input[1] == b'=' {
                Some((2, Token::Ge))
            } else {
                Some((1, Token::Gt))
            }
        }
        CHAR_ALPHABET | CHAR_UNDERSCORE => {
            let len = len_identifier(input);
            let id = &input[..len];
            const MAX_KEYWORD_LEN: usize = 7;
            if len <= MAX_KEYWORD_LEN {
                let mut lower_id = [0; MAX_KEYWORD_LEN];
                for (i, &byte) in id.iter().take(MAX_KEYWORD_LEN).enumerate() {
                    lower_id[i] = UPPER_TO_LOWER[byte as usize];
                }
                match &lower_id {
                    b"select\0" => Some((len, Token::Select)),
                    b"from\0\0\0" => Some((len, Token::From)),
                    b"where\0\0" => Some((len, Token::Where)),
                    b"create\0" => Some((len, Token::Create)),
                    b"table\0\0" => Some((len, Token::Table)),
                    b"index\0\0" => Some((len, Token::Index)),
                    b"primary" => Some((len, Token::Primary)),
                    b"key\0\0\0\0" => Some((len, Token::Key)),
                    b"on\0\0\0\0\0" => Some((len, Token::On)),
                    b"null\0\0\0" => Some((len, Token::Null)),
                    _ => Some((len, Token::Identifier(id))),
                }
            } else {
                Some((len, Token::Identifier(id)))
            }
        }
        CHAR_DIGIT => {
            let mut value = (input[0] - b'0') as i64;
            let mut len = 1;
            for &byte in input.iter().skip(1) {
                match CHAR_LOOKUP_TABLE[byte as usize] {
                    CHAR_DIGIT => {
                        value = value * 10 + (byte - b'0') as i64;
                        len += 1;
                    }
                    _ => break,
                }
            }
            Some((len, Token::Integer(value)))
        }
        CHAR_INVALID => Some((1, Token::Illegal)),
        c => {
            unreachable!("unexpected char code: ({}), char: {}", c, input[0]);
        }
    }
}

fn len_identifier(input_bytes: &[u8]) -> usize {
    // Skip the first byte since it is already checked.
    for (i, &byte) in input_bytes.iter().skip(1).enumerate() {
        if CHAR_LOOKUP_TABLE[byte as usize] > CHAR_DIGIT {
            return i + 1;
        }
    }
    input_bytes.len()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_special_characters() {
        for (c, token) in [
            ('(', Token::LeftParen),
            (')', Token::RightParen),
            ('*', Token::Asterisk),
            (',', Token::Comma),
            (';', Token::Semicolon),
        ] {
            let input = format!("{c}");
            assert_eq!(get_token(input.as_bytes()), Some((1, token)), "{}", input);
            let input = format!("{c}abc");
            assert_eq!(get_token(input.as_bytes()), Some((1, token)), "{}", input);
        }
    }

    #[test]
    fn test_space() {
        assert_eq!(get_token(b" a"), Some((1, Token::Space)));
        assert_eq!(get_token(b" "), Some((1, Token::Space)));
        assert_eq!(get_token(b"     a"), Some((5, Token::Space)));
        assert_eq!(get_token(b"     "), Some((5, Token::Space)));
    }

    #[test]
    fn test_identifier() {
        for c in 'a'..='z' {
            let input = format!("{c}");
            assert_eq!(
                get_token(input.as_bytes()),
                Some((1, Token::Identifier(input.as_bytes())))
            );
            let input = format!("{c}abc ");
            assert_eq!(
                get_token(input.as_bytes()),
                Some((4, Token::Identifier(&input.as_bytes()[..4])))
            );
        }
        let mut input = String::new();
        for c in 'a'..='z' {
            input.push(c);
        }
        input.push('_');
        for c in 'A'..='Z' {
            input.push(c);
        }
        for c in '0'..='9' {
            input.push(c);
        }
        input.push(' ');
        assert_eq!(
            get_token(input.as_bytes()),
            Some((input.len() - 1, Token::Identifier(&input.as_bytes()[..input.len() - 1])))
        );

        assert_eq!(get_token(b"_hello "), Some((6, Token::Identifier(b"_hello"))));
        assert_eq!(get_token(b"_ "), Some((1, Token::Identifier(b"_"))));
    }

    #[test]
    fn test_keywords() {
        for (keyword, token) in [
            ("select", Token::Select),
            ("from", Token::From),
            ("where", Token::Where),
            ("create", Token::Create),
            ("table", Token::Table),
            ("index", Token::Index),
            ("primary", Token::Primary),
            ("key", Token::Key),
            ("on", Token::On),
            ("null", Token::Null),
        ] {
            assert_eq!(get_token(keyword.as_bytes()), Some((keyword.len(), token)));
            let input = format!("{keyword} ");
            assert_eq!(get_token(input.as_bytes()), Some((keyword.len(), token)));
            let input = format!("{} ", keyword.to_uppercase());
            assert_eq!(get_token(input.as_bytes()), Some((keyword.len(), token)));
            let mut input = String::new();
            for (i, c) in keyword.chars().enumerate() {
                if i % 2 == 0 {
                    input.push(c.to_uppercase().next().unwrap());
                } else {
                    input.push(c);
                }
            }
            input.push(' ');
            assert_eq!(get_token(input.as_bytes()), Some((keyword.len(), token)));
            let input = format!("{keyword}a ");
            assert_eq!(
                get_token(input.as_bytes()),
                Some((input.len() - 1, Token::Identifier(&input.as_bytes()[..input.len() - 1])))
            );
        }
    }

    #[test]
    fn test_binary_operators() {
        for (s, token) in [
            ("!", Token::Illegal),
            ("!=", Token::Ne),
            ("<", Token::Lt),
            ("<=", Token::Le),
            ("<>", Token::Ne),
            ("=", Token::Eq),
            ("==", Token::Eq),
            (">", Token::Gt),
            (">=", Token::Ge),
        ] {
            let input = format!("{s}");
            assert_eq!(get_token(input.as_bytes()), Some((s.len(), token)), "{}", input);
            let input = format!("{s}abc");
            assert_eq!(get_token(input.as_bytes()), Some((s.len(), token)), "{}", input);
        }
    }

    #[test]
    fn test_get_token_no_space() {
        assert_eq!(get_token_no_space(b"   (  "), Some((4, Token::LeftParen)));
    }

    #[test]
    fn test_statement() {
        for (input, tokens) in [
            (
                "select * from table1;",
                vec![
                    Token::Select,
                    Token::Space,
                    Token::Asterisk,
                    Token::Space,
                    Token::From,
                    Token::Space,
                    Token::Identifier(b"table1"),
                    Token::Semicolon,
                ],
            ),
            (
                "select*from table1;",
                vec![
                    Token::Select,
                    Token::Asterisk,
                    Token::From,
                    Token::Space,
                    Token::Identifier(b"table1"),
                    Token::Semicolon,
                ],
            ),
            (
                "select   *    from   table_1   ;   ",
                vec![
                    Token::Select,
                    Token::Space,
                    Token::Asterisk,
                    Token::Space,
                    Token::From,
                    Token::Space,
                    Token::Identifier(b"table_1"),
                    Token::Space,
                    Token::Semicolon,
                    Token::Space,
                ],
            ),
            (
                "select(col1,col2)from table1;",
                vec![
                    Token::Select,
                    Token::LeftParen,
                    Token::Identifier(b"col1"),
                    Token::Comma,
                    Token::Identifier(b"col2"),
                    Token::RightParen,
                    Token::From,
                    Token::Space,
                    Token::Identifier(b"table1"),
                    Token::Semicolon,
                ],
            ),
            (
                "select(col1,col2)from table1 where col1=10;",
                vec![
                    Token::Select,
                    Token::LeftParen,
                    Token::Identifier(b"col1"),
                    Token::Comma,
                    Token::Identifier(b"col2"),
                    Token::RightParen,
                    Token::From,
                    Token::Space,
                    Token::Identifier(b"table1"),
                    Token::Space,
                    Token::Where,
                    Token::Space,
                    Token::Identifier(b"col1"),
                    Token::Eq,
                    Token::Integer(10),
                    Token::Semicolon,
                ],
            ),
            (
                "CREATE TABLE table1(col1, col2, col3 integer primary key);",
                vec![
                    Token::Create,
                    Token::Space,
                    Token::Table,
                    Token::Space,
                    Token::Identifier(b"table1"),
                    Token::LeftParen,
                    Token::Identifier(b"col1"),
                    Token::Comma,
                    Token::Space,
                    Token::Identifier(b"col2"),
                    Token::Comma,
                    Token::Space,
                    Token::Identifier(b"col3"),
                    Token::Space,
                    Token::Identifier(b"integer"),
                    Token::Space,
                    Token::Primary,
                    Token::Space,
                    Token::Key,
                    Token::RightParen,
                    Token::Semicolon,
                ],
            ),
            (
                "CREATE INDEX index1 on table1(col1, col2, col3);",
                vec![
                    Token::Create,
                    Token::Space,
                    Token::Index,
                    Token::Space,
                    Token::Identifier(b"index1"),
                    Token::Space,
                    Token::On,
                    Token::Space,
                    Token::Identifier(b"table1"),
                    Token::LeftParen,
                    Token::Identifier(b"col1"),
                    Token::Comma,
                    Token::Space,
                    Token::Identifier(b"col2"),
                    Token::Comma,
                    Token::Space,
                    Token::Identifier(b"col3"),
                    Token::RightParen,
                    Token::Semicolon,
                ],
            ),
        ] {
            let mut output_tokens = Vec::new();
            let mut input_bytes = input.as_bytes();
            while let Some((len, token)) = get_token(input_bytes) {
                output_tokens.push(token);
                input_bytes = &input_bytes[len..];
            }
            assert_eq!(output_tokens, tokens, "{}", input);
        }
    }
}
