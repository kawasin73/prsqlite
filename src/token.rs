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

use crate::utils::is_space;
use crate::utils::HexedBytes;
use crate::utils::MaybeQuotedBytes;
use crate::utils::UPPER_TO_LOWER;

const CHAR_X: u8 = 0x00;
const CHAR_ALPHABET: u8 = 0x01;
const CHAR_UNDERSCORE: u8 = 0x02;
const CHAR_DIGIT: u8 = 0x03;
const CHAR_DOLLAR: u8 = 0x04;
const CHAR_QUOTE: u8 = 0x05; // ", ', `
const CHAR_QUOTE2: u8 = 0x06; // [
const CHAR_INVALID: u8 = 0xFF;

static CHAR_LOOKUP_TABLE: [u8; 256] = [
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0x00 - 0x07
    0xFF, b' ', b' ', 0xFF, b' ', b' ', 0xFF, 0xFF, // 0x08 - 0x0F
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0x10 - 0x17
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0x18 - 0x1F
    b' ', b'!', 0x05, 0xFF, 0x04, 0xFF, 0xFF, 0x05, // 0x20 - 0x27
    b'(', b')', b'*', b'+', b',', b'-', b'.', 0xFF, // 0x28 - 0x2F
    0x03, 0x03, 0x03, 0x03, 0x03, 0x03, 0x03, 0x03, // 0x30 - 0x37
    0x03, 0x03, 0xFF, b';', b'<', b'=', b'>', 0xFF, // 0x38 - 0x3F
    0xFF, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, // 0x40 - 0x47
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, // 0x48 - 0x4F
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, // 0x50 - 0x57
    0x00, 0x01, 0x01, 0x06, 0xFF, 0xFF, 0xFF, 0x02, // 0x58 - 0x5F
    0x05, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, // 0x60 - 0x67
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, // 0x68 - 0x6F
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, // 0x70 - 0x77
    0x00, 0x01, 0x01, 0xFF, b'|', 0xFF, b'~', 0xFF, // 0x78 - 0x7F
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0x80 - 0x87
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0x88 - 0x8F
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0x90 - 0x97
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0x98 - 0x9F
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xA0 - 0xA7
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xA8 - 0xAF
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xB0 - 0xB7
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xB8 - 0xBF
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xC0 - 0xC7
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xC8 - 0xCF
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xD0 - 0xD7
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xD8 - 0xDF
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xE0 - 0xE7
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xE8 - 0xEF
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xF0 - 0xF7
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 0xF8 - 0xFF
];

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Token<'a> {
    // Keywords
    Select,
    As,
    From,
    Where,
    Create,
    Table,
    Index,
    Primary,
    Key,
    On,
    Null,
    Cast,

    // Symbols
    Space,
    LeftParen,
    RightParen,
    Asterisk,
    Plus,
    Comma,
    Minus,
    Dot,
    Semicolon,
    Tilda,

    // Operators
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
    BitOr,
    Concat,

    // Literals
    Identifier(MaybeQuotedBytes<'a>),
    String(MaybeQuotedBytes<'a>),
    Blob(HexedBytes<'a>),
    // Only contains 0-9 chars.
    Integer(&'a [u8]),
    Float(&'a [u8]),
    Illegal,
}

pub fn get_token(input: &[u8]) -> Option<(usize, Token)> {
    if input.is_empty() {
        return None;
    }
    match CHAR_LOOKUP_TABLE[input[0] as usize] {
        b' ' => {
            for (i, &byte) in input.iter().skip(1).enumerate() {
                if !is_space(byte) {
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
        b'+' => Some((1, Token::Plus)),
        b',' => Some((1, Token::Comma)),
        b'-' => Some((1, Token::Minus)),
        b'.' => {
            if input.len() >= 2 && input[1].is_ascii_digit() {
                let (len, valid) = len_float(input);
                if valid {
                    Some((len, Token::Float(&input[..len])))
                } else {
                    Some((len, Token::Illegal))
                }
            } else {
                Some((1, Token::Dot))
            }
        }
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
        b'|' => {
            if input.len() >= 2 && input[1] == b'|' {
                Some((2, Token::Concat))
            } else {
                Some((1, Token::BitOr))
            }
        }
        b'~' => Some((1, Token::Tilda)),
        CHAR_X => {
            if input.len() >= 2 && input[1] == b'\'' {
                let mut iter = input.iter().skip(2).enumerate();
                for (i, byte) in iter.by_ref() {
                    if byte.is_ascii_hexdigit() {
                        // This should be the hot path.
                        continue;
                    } else if *byte == b'\'' {
                        let len = i + 3;
                        if i % 2 == 0 {
                            return Some((len, Token::Blob((&input[2..i + 2]).into())));
                        } else {
                            return Some((len, Token::Illegal));
                        }
                    } else {
                        break;
                    }
                }
                // Vacuum invalid hex digits.
                for (i, byte) in iter {
                    if *byte == b'\'' {
                        return Some((i + 3, Token::Illegal));
                    }
                }
                Some((input.len(), Token::Illegal))
            } else {
                let len = len_identifier(input);
                let id = &input[..len];
                Some((len, Token::Identifier(id.into())))
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
                    b"as\0\0\0\0\0" => Some((len, Token::As)),
                    b"from\0\0\0" => Some((len, Token::From)),
                    b"where\0\0" => Some((len, Token::Where)),
                    b"create\0" => Some((len, Token::Create)),
                    b"table\0\0" => Some((len, Token::Table)),
                    b"index\0\0" => Some((len, Token::Index)),
                    b"primary" => Some((len, Token::Primary)),
                    b"key\0\0\0\0" => Some((len, Token::Key)),
                    b"on\0\0\0\0\0" => Some((len, Token::On)),
                    b"null\0\0\0" => Some((len, Token::Null)),
                    b"cast\0\0\0" => Some((len, Token::Cast)),
                    _ => Some((len, Token::Identifier(id.into()))),
                }
            } else {
                Some((len, Token::Identifier(id.into())))
            }
        }
        CHAR_DIGIT => {
            // TODO: support hexadecimal.
            let mut len = 1;
            for &byte in input.iter().skip(len) {
                // NOTE: u8::is_ascii_digit() is faster than CHAR_LOOKUP_TABLE.
                if byte.is_ascii_digit() {
                    len += 1;
                } else {
                    break;
                }
            }
            let (l, valid) = len_float(&input[len..]);
            if !valid {
                Some((len + l, Token::Illegal))
            } else if l == 0 {
                Some((len, Token::Integer(&input[..len])))
            } else {
                Some((len + l, Token::Float(&input[..len + l])))
            }
        }
        CHAR_QUOTE => {
            let delimiter = input[0];
            let mut iter = input.iter().enumerate().skip(1);
            while let Some((i, &byte)) = iter.next() {
                if byte == delimiter {
                    if let Some((_, &byte)) = iter.next() {
                        if byte == delimiter {
                            continue;
                        }
                    }
                    let quoted_buf = &input[..i + 1];
                    if delimiter == b'\'' {
                        return Some((i + 1, Token::String(quoted_buf.into())));
                    } else {
                        return Some((i + 1, Token::Identifier(quoted_buf.into())));
                    }
                }
            }
            Some((input.len(), Token::Illegal))
        }
        CHAR_QUOTE2 => {
            for (i, &byte) in input.iter().enumerate().skip(1) {
                if byte == b']' {
                    let unquoted_buf = &input[1..i];
                    return Some((i + 1, Token::Identifier(unquoted_buf.into())));
                }
            }
            Some((input.len(), Token::Illegal))
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
        if CHAR_LOOKUP_TABLE[byte as usize] > CHAR_DOLLAR {
            return i + 1;
        }
    }
    input_bytes.len()
}

fn len_float(input: &[u8]) -> (usize, bool) {
    let mut len = 0;
    if !input.is_empty() && input[0] == b'.' {
        len += 1;
        for &byte in input.iter().skip(len) {
            if byte.is_ascii_digit() {
                len += 1;
            } else {
                break;
            }
        }
    }
    if input.len() > len && (input[len] == b'e' || input[len] == b'E') {
        len += 1;
        let mut iter = input.iter().skip(len);
        let Some(&byte) = iter.next() else {
            return (len, false);
        };
        let mut byte = byte;
        if byte == b'+' || byte == b'-' {
            len += 1;
            if let Some(&b) = iter.next() {
                byte = b;
            } else {
                byte = 0;
            };
        }
        if byte.is_ascii_digit() {
            len += 1;
        } else {
            return (len, false);
        }
        for &byte in iter {
            if byte.is_ascii_digit() {
                len += 1;
            } else {
                break;
            }
        }
    }
    (len, true)
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
            ('+', Token::Plus),
            (',', Token::Comma),
            ('-', Token::Minus),
            ('.', Token::Dot),
            (';', Token::Semicolon),
            ('~', Token::Tilda),
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

        assert_eq!(get_token(b"\t"), Some((1, Token::Space)));
        assert_eq!(get_token(b"\n"), Some((1, Token::Space)));
        assert_eq!(get_token(b"\x0b"), Some((1, Token::Illegal)));
        assert_eq!(get_token(b"\x0c"), Some((1, Token::Space)));
        assert_eq!(get_token(b"\r"), Some((1, Token::Space)));
        assert_eq!(get_token(b"  \t\n\x0b\x0c\r\x0e"), Some((7, Token::Space)));
    }

    #[test]
    fn test_integer() {
        let mut test_cases = Vec::new();
        for i in 0..=1000 {
            test_cases.push(i.to_string());
        }
        for s in [
            "1234567890",
            "00",
            "001",
            "9223372036854775807",
            "9223372036854775808",
            "99999999999999999999",
        ] {
            test_cases.push(s.to_string());
        }
        for literal in test_cases {
            assert_eq!(
                get_token(literal.as_bytes()),
                Some((literal.len(), Token::Integer(literal.as_bytes()))),
                "literal: {}",
                literal
            );
            let input = format!("{literal}abc ");
            assert_eq!(
                get_token(input.as_bytes()),
                Some((literal.len(), Token::Integer(literal.as_bytes()))),
                "input: {}",
                input
            );
        }
    }

    #[test]
    fn test_float() {
        for literal in [
            "0.1",
            "0.01",
            "00.1",
            "0.1234567890",
            "1.",
            "0.",
            ".0",
            ".0123456789",
            "10e1",
            "10e+2",
            "10e-3",
            "00e1",
            "01e+2",
            "0.1e-3",
            "0.20e4",
            ".1e5",
            ".2e+6",
            ".34567e7",
            "1.e5",
            "2e0123456789",
        ] {
            assert_eq!(
                get_token(literal.as_bytes()),
                Some((literal.len(), Token::Float(literal.as_bytes()))),
                "literal: {}",
                literal
            );
            let input = format!("{literal}abc ");
            assert_eq!(
                get_token(input.as_bytes()),
                Some((literal.len(), Token::Float(literal.as_bytes()))),
                "input: {}",
                input
            );
        }
        assert_eq!(get_token(b"0.1.2"), Some((3, Token::Float(b"0.1"))));
    }

    #[test]
    fn test_numeric_failure() {
        assert_eq!(get_token(b"0.1e"), Some((4, Token::Illegal)));
        assert_eq!(get_token(b"0.1ee"), Some((4, Token::Illegal)));
        assert_eq!(get_token(b"0.1e+"), Some((5, Token::Illegal)));
        assert_eq!(get_token(b"0.1e+e"), Some((5, Token::Illegal)));
        assert_eq!(get_token(b"0.1e-"), Some((5, Token::Illegal)));
        assert_eq!(get_token(b"0.1e-e"), Some((5, Token::Illegal)));
        assert_eq!(get_token(b".e1"), Some((1, Token::Dot)));
        assert_eq!(
            get_token(b"e1"),
            Some((2, Token::Identifier(b"e1".as_slice().into())))
        );
    }

    #[test]
    fn test_identifier() {
        for c in 'a'..='z' {
            let input = format!("{c}");
            assert_eq!(
                get_token(input.as_bytes()),
                Some((
                    1,
                    Token::Identifier(MaybeQuotedBytes::from(input.as_bytes()))
                ))
            );
            let input = format!("{c}abc ");
            assert_eq!(
                get_token(input.as_bytes()),
                Some((
                    4,
                    Token::Identifier(MaybeQuotedBytes::from(&input.as_bytes()[..4]))
                ))
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
            Some((
                input.len() - 1,
                Token::Identifier(MaybeQuotedBytes::from(&input.as_bytes()[..input.len() - 1]))
            ))
        );

        assert_eq!(
            get_token(b"_hello "),
            Some((6, Token::Identifier(b"_hello".as_slice().into())))
        );
        assert_eq!(
            get_token(b"_ "),
            Some((1, Token::Identifier(b"_".as_slice().into())))
        );
        assert_eq!(
            get_token(b"hello$ "),
            Some((6, Token::Identifier(b"hello$".as_slice().into())))
        );
    }

    #[test]
    fn test_quoted_identifier() {
        assert_eq!(
            get_token(b"`hello` "),
            Some((7, Token::Identifier(b"`hello`".as_slice().into())))
        );
        // Non-ASCII
        assert_eq!(
            get_token(b"`\xE3\x81\x82` "),
            Some((5, Token::Identifier(b"`\xE3\x81\x82`".as_slice().into())))
        );
        assert_eq!(
            get_token(b"``hello`` "),
            Some((2, Token::Identifier(b"``".as_slice().into())))
        );
        assert_eq!(
            get_token(b"`\"hello\"` "),
            Some((9, Token::Identifier(b"`\"hello\"`".as_slice().into())))
        );
        assert_eq!(
            get_token(b"`hello`aaa` "),
            Some((7, Token::Identifier(b"`hello`".as_slice().into())))
        );
        assert_eq!(
            get_token(b"`hello``aaa ` "),
            Some((13, Token::Identifier(b"`hello``aaa `".as_slice().into())))
        );
        assert_eq!(
            get_token(b"`hello```aaa  "),
            Some((9, Token::Identifier(b"`hello```".as_slice().into())))
        );

        // Non-ASCII
        assert_eq!(
            get_token(b"\"\xE3\x81\x82\" "),
            Some((5, Token::Identifier(b"\"\xE3\x81\x82\"".as_slice().into())))
        );
        assert_eq!(
            get_token(b"\"hello\" "),
            Some((7, Token::Identifier(b"\"hello\"".as_slice().into())))
        );
        assert_eq!(
            get_token(b"\"\"hello "),
            Some((2, Token::Identifier(b"\"\"".as_slice().into())))
        );
        assert_eq!(
            get_token(b"\"`hello`\" "),
            Some((9, Token::Identifier(b"\"`hello`\"".as_slice().into())))
        );
        assert_eq!(
            get_token(b"\"hello\"aaa\" "),
            Some((7, Token::Identifier(b"\"hello\"".as_slice().into())))
        );
        assert_eq!(
            get_token(b"\"hello\"\"aaa \" "),
            Some((
                13,
                Token::Identifier(b"\"hello\"\"aaa \"".as_slice().into())
            ))
        );
        assert_eq!(
            get_token(b"\"hello\"\"\"aaa  "),
            Some((9, Token::Identifier(b"\"hello\"\"\"".as_slice().into())))
        );

        assert_eq!(
            get_token(b"[hello]] "),
            Some((7, Token::Identifier(b"hello".as_slice().into())))
        );
        // Non-ASCII
        assert_eq!(
            get_token(b"[\xE3\x81\x82] "),
            Some((5, Token::Identifier(b"\xE3\x81\x82".as_slice().into())))
        );
        assert_eq!(
            get_token(b"[[he[llo[]]] "),
            Some((10, Token::Identifier(b"[he[llo[".as_slice().into())))
        );

        assert_eq!(get_token(b"`hello\" "), Some((8, Token::Illegal)));
        assert_eq!(get_token(b"`hello`` "), Some((9, Token::Illegal)));
        assert_eq!(get_token(b"`hello````aaa  "), Some((15, Token::Illegal)));

        assert_eq!(get_token(b"\"hello` "), Some((8, Token::Illegal)));
        assert_eq!(get_token(b"\"hello\"\" "), Some((9, Token::Illegal)));
        assert_eq!(
            get_token(b"\"hello\"\"\"\"aaa  "),
            Some((15, Token::Illegal))
        );

        assert_eq!(get_token(b"[hello "), Some((7, Token::Illegal)));
    }

    #[test]
    fn test_string() {
        assert_eq!(
            get_token(b"'hello' "),
            Some((7, Token::String(b"'hello'".as_slice().into())))
        );
        // Non-ASCII
        assert_eq!(
            get_token(b"'\xE3\x81\x82' "),
            Some((5, Token::String(b"'\xE3\x81\x82'".as_slice().into())))
        );
        assert_eq!(
            get_token(b"''hello'' "),
            Some((2, Token::String(b"''".as_slice().into())))
        );
        assert_eq!(
            get_token(b"'\"hello\"' "),
            Some((9, Token::String(b"'\"hello\"'".as_slice().into())))
        );
        assert_eq!(
            get_token(b"'hello'aaa' "),
            Some((7, Token::String(b"'hello'".as_slice().into())))
        );
        assert_eq!(
            get_token(b"'hello''aaa ' "),
            Some((13, Token::String(b"'hello''aaa '".as_slice().into())))
        );
        assert_eq!(
            get_token(b"'hello'''aaa  "),
            Some((9, Token::String(b"'hello'''".as_slice().into())))
        );

        assert_eq!(get_token(b"'hello\" "), Some((8, Token::Illegal)));
        assert_eq!(get_token(b"'hello'' "), Some((9, Token::Illegal)));
        assert_eq!(get_token(b"'hello''''aaa  "), Some((15, Token::Illegal)));
    }

    #[test]
    fn test_keywords() {
        for (keyword, token) in [
            ("select", Token::Select),
            ("as", Token::As),
            ("from", Token::From),
            ("where", Token::Where),
            ("create", Token::Create),
            ("table", Token::Table),
            ("index", Token::Index),
            ("primary", Token::Primary),
            ("key", Token::Key),
            ("on", Token::On),
            ("null", Token::Null),
            ("cast", Token::Cast),
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
                Some((
                    input.len() - 1,
                    Token::Identifier(MaybeQuotedBytes::from(&input.as_bytes()[..input.len() - 1]))
                ))
            );
        }
    }

    #[test]
    fn test_blob() {
        assert_eq!(
            get_token(b"x'0123456789abcdef' "),
            Some((19, Token::Blob(b"0123456789abcdef".as_slice().into())))
        );
        assert_eq!(
            get_token(b"X'0123456789abcdef' "),
            Some((19, Token::Blob(b"0123456789abcdef".as_slice().into())))
        );
        assert_eq!(
            get_token(b"x'' "),
            Some((3, Token::Blob(b"".as_slice().into())))
        );
        assert_eq!(
            get_token(b"X'' "),
            Some((3, Token::Blob(b"".as_slice().into())))
        );
    }

    #[test]
    fn test_blob_fail() {
        // Invalid length
        assert_eq!(
            get_token(b"x'0123456789abcde' "),
            Some((18, Token::Illegal))
        );
        assert_eq!(
            get_token(b"X'0123456789abcde' "),
            Some((18, Token::Illegal))
        );
        // Invalid digit
        assert_eq!(get_token(b"x'fg' "), Some((5, Token::Illegal)));
        assert_eq!(get_token(b"X'fg' "), Some((5, Token::Illegal)));
        assert_eq!(
            get_token(b"x'g123456789abcdef' "),
            Some((19, Token::Illegal))
        );
        assert_eq!(
            get_token(b"X'g123456789abcdef' "),
            Some((19, Token::Illegal))
        );

        // No end
        assert_eq!(get_token(b"x'"), Some((2, Token::Illegal)));
        assert_eq!(get_token(b"X'"), Some((2, Token::Illegal)));
        assert_eq!(get_token(b"x'0123456789abcdef"), Some((18, Token::Illegal)));
        assert_eq!(get_token(b"X'0123456789abcdef"), Some((18, Token::Illegal)));
        // No end + invalid digit
        assert_eq!(
            get_token(b"x'0123456789abcdefg"),
            Some((19, Token::Illegal))
        );
        assert_eq!(
            get_token(b"X'0123456789abcdefg"),
            Some((19, Token::Illegal))
        );
        assert_eq!(
            get_token(b"x' 123456789abcdefg"),
            Some((19, Token::Illegal))
        );
        assert_eq!(
            get_token(b"X' 123456789abcdefg"),
            Some((19, Token::Illegal))
        );
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
            ("|", Token::BitOr),
            ("||", Token::Concat),
        ] {
            let input = s.to_string();
            assert_eq!(
                get_token(input.as_bytes()),
                Some((s.len(), token)),
                "{}",
                input
            );
            let input = format!("{s}abc");
            assert_eq!(
                get_token(input.as_bytes()),
                Some((s.len(), token)),
                "{}",
                input
            );
        }
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
                    Token::Identifier(b"table1".as_slice().into()),
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
                    Token::Identifier(b"table1".as_slice().into()),
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
                    Token::Identifier(b"table_1".as_slice().into()),
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
                    Token::Identifier(b"col1".as_slice().into()),
                    Token::Comma,
                    Token::Identifier(b"col2".as_slice().into()),
                    Token::RightParen,
                    Token::From,
                    Token::Space,
                    Token::Identifier(b"table1".as_slice().into()),
                    Token::Semicolon,
                ],
            ),
            (
                "select(col1,col2)from table1 where col1=10;",
                vec![
                    Token::Select,
                    Token::LeftParen,
                    Token::Identifier(b"col1".as_slice().into()),
                    Token::Comma,
                    Token::Identifier(b"col2".as_slice().into()),
                    Token::RightParen,
                    Token::From,
                    Token::Space,
                    Token::Identifier(b"table1".as_slice().into()),
                    Token::Space,
                    Token::Where,
                    Token::Space,
                    Token::Identifier(b"col1".as_slice().into()),
                    Token::Eq,
                    Token::Integer("10".as_bytes()),
                    Token::Semicolon,
                ],
            ),
            (
                "select(col1,col2 as col3)from table1 where \"col1\"=1.1;",
                vec![
                    Token::Select,
                    Token::LeftParen,
                    Token::Identifier(b"col1".as_slice().into()),
                    Token::Comma,
                    Token::Identifier(b"col2".as_slice().into()),
                    Token::Space,
                    Token::As,
                    Token::Space,
                    Token::Identifier(b"col3".as_slice().into()),
                    Token::RightParen,
                    Token::From,
                    Token::Space,
                    Token::Identifier(b"table1".as_slice().into()),
                    Token::Space,
                    Token::Where,
                    Token::Space,
                    Token::Identifier(b"\"col1\"".as_slice().into()),
                    Token::Eq,
                    Token::Float("1.1".as_bytes()),
                    Token::Semicolon,
                ],
            ),
            (
                "select(\"col1\",`col2`)from table1 where [col1]='hello world';",
                vec![
                    Token::Select,
                    Token::LeftParen,
                    Token::Identifier(b"\"col1\"".as_slice().into()),
                    Token::Comma,
                    Token::Identifier(b"`col2`".as_slice().into()),
                    Token::RightParen,
                    Token::From,
                    Token::Space,
                    Token::Identifier(b"table1".as_slice().into()),
                    Token::Space,
                    Token::Where,
                    Token::Space,
                    Token::Identifier(b"col1".as_slice().into()),
                    Token::Eq,
                    Token::String(b"'hello world'".as_slice().into()),
                    Token::Semicolon,
                ],
            ),
            (
                "select(\"col1\",`col2`)from table1 where `col1`=x'0123456789abcdef';",
                vec![
                    Token::Select,
                    Token::LeftParen,
                    Token::Identifier(b"\"col1\"".as_slice().into()),
                    Token::Comma,
                    Token::Identifier(b"`col2`".as_slice().into()),
                    Token::RightParen,
                    Token::From,
                    Token::Space,
                    Token::Identifier(b"table1".as_slice().into()),
                    Token::Space,
                    Token::Where,
                    Token::Space,
                    Token::Identifier(b"`col1`".as_slice().into()),
                    Token::Eq,
                    Token::Blob(b"0123456789abcdef".as_slice().into()),
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
                    Token::Identifier(b"table1".as_slice().into()),
                    Token::LeftParen,
                    Token::Identifier(b"col1".as_slice().into()),
                    Token::Comma,
                    Token::Space,
                    Token::Identifier(b"col2".as_slice().into()),
                    Token::Comma,
                    Token::Space,
                    Token::Identifier(b"col3".as_slice().into()),
                    Token::Space,
                    Token::Identifier(b"integer".as_slice().into()),
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
                    Token::Identifier(b"index1".as_slice().into()),
                    Token::Space,
                    Token::On,
                    Token::Space,
                    Token::Identifier(b"table1".as_slice().into()),
                    Token::LeftParen,
                    Token::Identifier(b"col1".as_slice().into()),
                    Token::Comma,
                    Token::Space,
                    Token::Identifier(b"col2".as_slice().into()),
                    Token::Comma,
                    Token::Space,
                    Token::Identifier(b"col3".as_slice().into()),
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
