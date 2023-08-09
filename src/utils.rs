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

use std::hash::{Hash, Hasher};

const VARINT_FLAG_MASK: u8 = 0b1000_0000;
const VARINT_VAR_MASK: u8 = !VARINT_FLAG_MASK;

/// Parse varint.
///
/// Return None if the buffer is not valid varint.
pub fn parse_varint(buf: &[u8]) -> Option<(i64, usize)> {
    if valid_varint_buffer(buf) {
        Some(unsafe_parse_varint(buf))
    } else {
        None
    }
}

fn valid_varint_buffer(buf: &[u8]) -> bool {
    let mut count = 0;
    for b in buf {
        count += 1;
        if count == 9 || b & VARINT_FLAG_MASK == 0 {
            return true;
        }
    }
    false
}

/// Parse varint without validation
pub fn unsafe_parse_varint(buf: &[u8]) -> (i64, usize) {
    if buf[0] & VARINT_FLAG_MASK == 0 {
        (buf[0] as i64, 1)
    } else {
        let mut v = (buf[0] & VARINT_VAR_MASK) as i64;
        #[allow(clippy::needless_range_loop)]
        for i in 1..8 {
            v <<= 7;
            v |= (buf[i] & VARINT_VAR_MASK) as i64;
            if buf[i] & VARINT_FLAG_MASK == 0 {
                return (v, i + 1);
            }
        }
        v <<= 8;
        v |= buf[8] as i64;
        (v, 9)
    }
}

/// Parse integer literal.
///
/// Returns -1 if it is 9223372036854775808. If it exceeds i64 range, it returns
/// i64::MIN.
///
/// All bytes must be ascii digit.
pub fn parse_integer_literal(input: &[u8]) -> i64 {
    assert!(!input.is_empty());

    // Skip leading zeros
    let mut n_zeros = input.len();
    for (i, byte) in input.iter().enumerate() {
        if *byte != b'0' {
            n_zeros = i;
            break;
        }
    }
    // i64::MAX is 19 digits. Parsing more than 19 digits cause u64 overflow.
    if input.len() - n_zeros > 19 {
        return i64::MIN;
    }

    let mut v = 0_u64;
    for &byte in input[n_zeros..].iter() {
        assert!(byte.is_ascii_digit());
        v = v * 10 + (byte - b'0') as u64;
    }

    if v <= i64::MAX as u64 {
        v as i64
    } else if v == i64::MAX as u64 + 1 {
        -1
    } else {
        i64::MIN
    }
}

/// Parse float literal.
///
/// The input must satisfy either of these conditions otherwise that must be
/// parsed as an integer literal:
///
/// * Contains '.'
/// * Contains 'e' or 'E'
/// * Overflows i64 range
///
/// input must not be empty.
///
/// input must not contains `0` value.
///
/// This is compatible with `sqlite3AtoF()` in SQLite except this only support
/// utf8.
pub fn parse_float_literal(input: &[u8]) -> f64 {
    assert!(!input.is_empty());
    let mut iter = input.iter();
    let mut byte = *iter.next().unwrap();

    // Skip leading zeros
    while byte == b'0' {
        // 0 only literal is not a float literal.
        byte = *iter.next().unwrap();
    }
    let mut significand = 0;
    let mut dicimal_point: i64 = 0;

    // Parse integer part
    while byte.is_ascii_digit() {
        significand = significand * 10 + (byte - b'0') as i64;
        // input must have more characters since this is not an integer literal.
        byte = *iter.next().unwrap();
        if significand >= (i64::MAX - 9) / 10 {
            while byte.is_ascii_digit() {
                dicimal_point += 1;
                let Some(&b) = iter.next() else {
                    byte = 0;
                    break;
                };
                byte = b;
            }
        }
    }

    // Parse fractional part
    if byte == b'.' {
        while {
            if let Some(&b) = iter.next() {
                byte = b;
            } else {
                byte = 0;
            };
            byte.is_ascii_digit()
        } {
            if significand < (i64::MAX - 9) / 10 {
                significand = significand * 10 + (byte - b'0') as i64;
                dicimal_point -= 1;
            }
        }
    }

    // Parse exponent part
    if byte != 0 {
        assert!(byte == b'e' || byte == b'E');
        byte = *iter.next().unwrap();
        let exponent_sign = match byte {
            b'+' => {
                byte = *iter.next().unwrap();
                1
            }
            b'-' => {
                byte = *iter.next().unwrap();
                -1
            }
            _ => 1,
        };
        assert!(byte.is_ascii_digit());
        let mut exponent = (byte - b'0') as i32;
        for b in iter {
            assert!(b.is_ascii_digit());
            exponent = if exponent < 10000 {
                exponent * 10 + (b - b'0') as i32
            } else {
                10000
            };
        }
        dicimal_point += (exponent * exponent_sign) as i64;
        byte = 0;
    } else {
        assert!(iter.next().is_none());
    }

    assert_eq!(byte, 0, "float value {:?} was not fully consumed", input);

    // Attempt to reduce exponent.
    loop {
        // TODO: Further optimization based on the truth that the sign of dicimal_point
        // is never changed.
        if dicimal_point > 0 && significand < i64::MAX / 10 {
            significand *= 10;
            dicimal_point -= 1;
        } else if dicimal_point < 0 && significand % 10 == 0 {
            significand /= 10;
            dicimal_point += 1;
        } else {
            break;
        }
    }

    // TODO: Further optimization. I'm not sure why 307, 342 from sqlite src/util.c
    // source code gives better performance...
    match dicimal_point.try_into() {
        Ok(dicimal_point) => significand as f64 * 10.0f64.powi(dicimal_point),
        Err(_) => {
            if dicimal_point > 0 {
                f64::INFINITY
            } else {
                0.0
            }
        }
    }
}

/// Converts a single byte to its uppercase equivalent.
///
/// This only support ascii characters conversion (i.e. 0 ~ 127).
pub static UPPER_TO_LOWER: [u8; 256] = [
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, // 0x00 - 0x07
    0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, // 0x08 - 0x0F
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, // 0x10 - 0x17
    0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, // 0x18 - 0x1F
    0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, // 0x20 - 0x27
    0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, // 0x28 - 0x2F
    0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, // 0x30 - 0x37
    0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, // 0x38 - 0x3F
    0x40, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, // 0x40 - 0x47
    0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, // 0x48 - 0x4F
    0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, // 0x50 - 0x57
    0x78, 0x79, 0x7A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, // 0x58 - 0x5F
    0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, // 0x60 - 0x67
    0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, // 0x68 - 0x6F
    0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, // 0x70 - 0x77
    0x78, 0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x7F, // 0x78 - 0x7F
    0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, // 0x80 - 0x87
    0x88, 0x89, 0x8A, 0x8B, 0x8C, 0x8D, 0x8E, 0x8F, // 0x88 - 0x8F
    0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, // 0x90 - 0x97
    0x98, 0x99, 0x9A, 0x9B, 0x9C, 0x9D, 0x9E, 0x9F, // 0x98 - 0x9F
    0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6, 0xA7, // 0xA0 - 0xA7
    0xA8, 0xA9, 0xAA, 0xAB, 0xAC, 0xAD, 0xAE, 0xAF, // 0xA8 - 0xAF
    0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, // 0xB0 - 0xB7
    0xB8, 0xB9, 0xBA, 0xBB, 0xBC, 0xBD, 0xBE, 0xBF, // 0xB8 - 0xBF
    0xC0, 0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7, // 0xC0 - 0xC7
    0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF, // 0xC8 - 0xCF
    0xD0, 0xD1, 0xD2, 0xD3, 0xD4, 0xD5, 0xD6, 0xD7, // 0xD0 - 0xD7
    0xD8, 0xD9, 0xDA, 0xDB, 0xDC, 0xDD, 0xDE, 0xDF, // 0xD8 - 0xDF
    0xE0, 0xE1, 0xE2, 0xE3, 0xE4, 0xE5, 0xE6, 0xE7, // 0xE0 - 0xE7
    0xE8, 0xE9, 0xEA, 0xEB, 0xEC, 0xED, 0xEE, 0xEF, // 0xE8 - 0xEF
    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6, 0xF7, // 0xF0 - 0xF7
    0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF, // 0xF8 - 0xFF
];

pub fn upper_to_lower(buf: &mut [u8]) {
    for b in buf {
        *b = UPPER_TO_LOWER[*b as usize];
    }
}

/// A wrapper for bytes to compare each other case insensitively with zero
/// allocation.
#[derive(Eq)]
pub struct CaseInsensitiveBytes<'a>(&'a [u8]);

impl CaseInsensitiveBytes<'_> {
    /// Compare with lower case bytes.
    pub fn equal_to_lower_bytes(&self, other: &[u8]) -> bool {
        if self.0.len() != other.len() {
            return false;
        }
        for (i, b) in self.0.iter().enumerate() {
            if UPPER_TO_LOWER[*b as usize] != other[i] {
                return false;
            }
        }
        true
    }

    /// Return whether this contains the `other` case insensitively.
    ///
    /// The other must be lower case.
    pub fn contains_lower_bytes(&self, other: &[u8]) -> bool {
        if other.is_empty() {
            return true;
        } else if self.0.len() < other.len() {
            return false;
        }

        'main_loop: for (i, b) in self
            .0
            .iter()
            .take(self.0.len() - other.len() + 1)
            .enumerate()
        {
            if UPPER_TO_LOWER[*b as usize] == other[0] {
                for (j, other_b) in other.iter().skip(1).enumerate() {
                    if UPPER_TO_LOWER[self.0[i + 1 + j] as usize] != *other_b {
                        continue 'main_loop;
                    }
                }
                return true;
            }
        }
        false
    }
}

impl<'a> From<&'a [u8]> for CaseInsensitiveBytes<'a> {
    fn from(bytes: &'a [u8]) -> Self {
        Self(bytes)
    }
}

impl<'a> From<&'a Vec<u8>> for CaseInsensitiveBytes<'a> {
    fn from(bytes: &'a Vec<u8>) -> Self {
        Self(&bytes[..])
    }
}

impl PartialEq for CaseInsensitiveBytes<'_> {
    fn eq(&self, other: &Self) -> bool {
        if self.0.len() != other.0.len() {
            return false;
        }
        for (i, b) in self.0.iter().enumerate() {
            if UPPER_TO_LOWER[*b as usize] != UPPER_TO_LOWER[other.0[i] as usize] {
                return false;
            }
        }
        true
    }
}

impl Hash for CaseInsensitiveBytes<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for b in self.0.iter() {
            state.write_u8(UPPER_TO_LOWER[*b as usize]);
        }
    }
}

/// A wrapper for bytes which may be quoted string.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct MaybeQuotedBytes<'a>(&'a [u8]);

impl MaybeQuotedBytes<'_> {
    /// Copy the dequoted text to newly allocated Vec<u8>.
    ///
    /// The double delimiter in the quoted text will be converted to single.
    ///
    /// If the text is not quoted, the returned Vec<u8> is the same as the
    /// original one.
    pub fn dequote(&self) -> Vec<u8> {
        match self.0.first() {
            Some(&b'\'') | Some(&b'"') | Some(&b'`') => {
                let delimiter = self.0[0];
                assert!(self.0.len() >= 2);
                assert_eq!(self.0[self.0.len() - 1], delimiter);
                let mut result = Vec::with_capacity(self.0.len() - 2);
                let mut iter = self.0[1..self.0.len() - 1].iter();
                while let Some(&b) = iter.next() {
                    if b == delimiter {
                        let next = iter.next();
                        assert_eq!(*next.unwrap(), delimiter);
                    }
                    result.push(b);
                }
                result
            }
            _ => self.0.to_vec(),
        }
    }

    pub fn dequote_iter(&self) -> DequotedIter<'_> {
        let delimiter = self
            .0
            .first()
            .map(|v| match v {
                b'\'' | b'"' | b'`' => *v,
                _ => 0,
            })
            .unwrap_or(0);
        let buf = if delimiter != 0 {
            &self.0[1..self.0.len() - 1]
        } else {
            self.0
        };
        DequotedIter {
            iter: buf.iter(),
            delimiter,
        }
    }

    pub fn raw(&self) -> &[u8] {
        self.0
    }
}

impl<'a> From<&'a [u8]> for MaybeQuotedBytes<'a> {
    fn from(bytes: &'a [u8]) -> Self {
        Self(bytes)
    }
}

pub struct DequotedIter<'a> {
    iter: std::slice::Iter<'a, u8>,
    delimiter: u8,
}

impl<'a> Iterator for DequotedIter<'a> {
    type Item = &'a u8;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(b) = self.iter.next() {
            if *b == self.delimiter {
                self.iter.next()
            } else {
                Some(b)
            }
        } else {
            None
        }
    }
}

/// Convert 1 byte ascii hexadecimal character to integer.
///
/// The input must be a valid hexadecimal character, i.e. 0-9, a-f, A-F.
///
/// This function is copied from sqlite3HexToInt().
pub fn hex_to_int(h: u8) -> u8 {
    assert!(h.is_ascii_hexdigit());
    let mut h = h;
    h += 9 * (1 & (h >> 6));
    h & 0x0f
}

/// A wrapper for bytes which is hexadecimal data.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct HexedBytes<'a>(&'a [u8]);

impl HexedBytes<'_> {
    pub fn decode(&self) -> Vec<u8> {
        assert!(self.0.len() % 2 == 0);
        let mut result = Vec::with_capacity(self.0.len() / 2);
        let mut iter = self.0.iter();
        // TODO: Optimization to avoid bounds check.
        while let Some(&b) = iter.next() {
            let high = hex_to_int(b);
            let low = hex_to_int(*iter.next().unwrap());
            result.push(high << 4 | low);
        }
        result
    }
}

impl<'a> From<&'a [u8]> for HexedBytes<'a> {
    fn from(bytes: &'a [u8]) -> Self {
        assert!(bytes.len() % 2 == 0);
        Self(bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_varint() {
        for (buf, v) in [
            ([0].as_ref(), 0),
            (&[1], 1),
            (&[127], 127),
            (&[129, 0], 0b1000_0000),
            (&[254, 127], 0b11_1111_0111_1111),
            (&[254, 254, 127], 0b1_1111_1011_1111_0111_1111),
            (&[254, 254, 254, 127], 0b1111_1101_1111_1011_1111_0111_1111),
            (
                &[254, 254, 254, 254, 127],
                0b111_1110_1111_1101_1111_1011_1111_0111_1111,
            ),
            (
                &[254, 254, 254, 254, 254, 127],
                0b11_1111_0111_1110_1111_1101_1111_1011_1111_0111_1111,
            ),
            (
                &[254, 254, 254, 254, 254, 254, 127],
                0b1_1111_1011_1111_0111_1110_1111_1101_1111_1011_1111_0111_1111,
            ),
            (
                &[254, 254, 254, 254, 254, 254, 254, 127],
                0b1111_1101_1111_1011_1111_0111_1110_1111_1101_1111_1011_1111_0111_1111,
            ),
            (
                &[192, 128, 128, 128, 128, 128, 128, 128, 1],
                -9223372036854775807,
            ),
            (&[255, 255, 255, 255, 255, 255, 255, 255, 255], -1),
        ] {
            let (result, consumed) = unsafe_parse_varint(buf);
            assert_eq!(consumed, buf.len(), "buf: {buf:?}");
            assert_eq!(result, v, "buf: {buf:?}");

            // valid as varint
            assert!(parse_varint(buf).is_some());
        }
    }

    #[test]
    fn test_parse_varint_consume() {
        let (_, consumed) = unsafe_parse_varint(&[0, 0]);
        assert_eq!(consumed, 1);
        let (_, consumed) = unsafe_parse_varint(&[129, 0, 0]);
        assert_eq!(consumed, 2);
        let (_, consumed) =
            unsafe_parse_varint(&[255, 255, 255, 255, 255, 255, 255, 255, 255, 255]);
        assert_eq!(consumed, 9);
    }

    #[test]
    fn test_parse_varint_invalid_varint() {
        for buf in [
            &[],
            &[128],
            &[255],
            &[255, 255],
            &[255, 255, 255],
            &[255, 255, 255, 255],
            &[255, 255, 255, 255, 255],
            &[255, 255, 255, 255, 255, 255],
            &[255, 255, 255, 255, 255, 255, 255],
            &[255, 255, 255, 255, 255, 255, 255, 255],
        ] as [&[u8]; 10]
        {
            assert!(parse_varint(buf).is_none());
        }
    }

    #[test]
    fn test_parse_integer_literal() {
        let mut test_cases = Vec::new();
        for i in 0..=1000 {
            test_cases.push((i.to_string(), i));
        }
        for (l, v) in [
            ("0", 0),
            ("00", 0),
            ("00000000000000000000", 0),
            ("000000000000000000001", 1),
            ("9223372036854775807", 9223372036854775807),
            ("9223372036854775808", -1),
            ("9223372036854775809", i64::MIN),
            ("9999999999999999999", i64::MIN),
        ] {
            test_cases.push((l.to_string(), v));
        }
        for (literal, value) in test_cases {
            assert_eq!(
                parse_integer_literal(literal.as_bytes()),
                value,
                "literal: {}",
                literal
            );
        }
    }

    #[test]
    fn test_parse_float_literal() {
        for (literal, value) in [
            ("0.1", 0.1),
            ("0.01", 0.01),
            ("00.1", 00.1),
            ("0.1234567890", 0.12345678900000001),
            ("1.", 1.),
            ("0.", 0.0),
            (".0", 0.0),
            (".0123456789", 0.0123456789),
            ("10e1", 10e1),
            ("12e+2", 12e+2),
            ("1234e-3", 1234e-3),
            ("00e1", 00e1),
            ("01e+2", 01e+2),
            ("0.1e-3", 0.1e-3),
            ("1.e12", 1.0e12),
            ("0.20e10", 0.20e10),
            (".1e5", 0.1e5),
            (".2e+6", 0.2e+6),
            (".34567e7", 0.34567e7),
            ("1.e5", 1.0e5),
            ("2e0123456789", f64::INFINITY),
            ("1e10000", f64::INFINITY),
            ("1e-10000", 0.0),
            ("9223372036854775807", 9223372036854775808.0),
            ("9223372036854775808", 9223372036854775808.0),
            ("9223372036854775808", i64::MAX as f64),
            ("9999999999999999999", 9999999999999999999.0),
            ("922337203685477580.0", 922337203685477580.0),
            // "SELECT 922337203685477580.0e-10" show 92233720.3685478 in sqlite.
            ("922337203685477580.0e-10", 92233720.36854777),
        ] {
            assert_eq!(
                parse_float_literal(literal.as_bytes()),
                value,
                "literal: {}",
                literal
            );
        }
        assert_eq!(parse_float_literal("1.23".as_bytes()), 1.23);
    }

    #[test]
    fn test_upper_to_lower_table() {
        for c in b'A'..=b'Z' {
            assert_eq!(UPPER_TO_LOWER[c as usize], c + (b'a' - b'A'));
        }
        for c in u8::MIN..=u8::MAX {
            if c.is_ascii_uppercase() {
                continue;
            }
            assert_eq!(UPPER_TO_LOWER[c as usize], c);
        }
    }

    #[test]
    fn test_case_insensitive_bytes() {
        assert!(
            CaseInsensitiveBytes::from("".as_bytes())
                == (CaseInsensitiveBytes::from("".as_bytes()))
        );
        assert!(
            CaseInsensitiveBytes::from("abc".as_bytes())
                != (CaseInsensitiveBytes::from("abcd".as_bytes()))
        );
        assert!(
            CaseInsensitiveBytes::from("abc".as_bytes())
                == (CaseInsensitiveBytes::from("abc".as_bytes()))
        );
        assert!(
            CaseInsensitiveBytes::from("ABc".as_bytes())
                == (CaseInsensitiveBytes::from("aBC".as_bytes()))
        );
        assert!(
            CaseInsensitiveBytes::from("abc".as_bytes())
                != (CaseInsensitiveBytes::from("abd".as_bytes()))
        );
    }

    #[test]
    fn test_equal_to_lower_bytes() {
        assert!(CaseInsensitiveBytes::from("".as_bytes()).equal_to_lower_bytes("".as_bytes()));
        assert!(
            !CaseInsensitiveBytes::from("abc".as_bytes()).equal_to_lower_bytes("abcd".as_bytes())
        );
        assert!(CaseInsensitiveBytes::from("abc".as_bytes()).equal_to_lower_bytes("abc".as_bytes()));
        assert!(CaseInsensitiveBytes::from("ABC".as_bytes()).equal_to_lower_bytes("abc".as_bytes()));
        assert!(CaseInsensitiveBytes::from("AbC".as_bytes()).equal_to_lower_bytes("abc".as_bytes()));
        // If the other part is not lower case, it always returns false.
        assert!(
            !CaseInsensitiveBytes::from("abc".as_bytes()).equal_to_lower_bytes("Abc".as_bytes())
        );
    }

    #[test]
    fn test_contains_lower_bytes() {
        assert!(CaseInsensitiveBytes::from("".as_bytes()).contains_lower_bytes("".as_bytes()));
        assert!(CaseInsensitiveBytes::from("abc".as_bytes()).contains_lower_bytes("".as_bytes()));
        assert!(CaseInsensitiveBytes::from("abc".as_bytes()).contains_lower_bytes("a".as_bytes()));
        assert!(CaseInsensitiveBytes::from("cba".as_bytes()).contains_lower_bytes("a".as_bytes()));
        assert!(CaseInsensitiveBytes::from("abc".as_bytes()).contains_lower_bytes("abc".as_bytes()));
        assert!(CaseInsensitiveBytes::from("ABC".as_bytes()).contains_lower_bytes("abc".as_bytes()));
        assert!(
            CaseInsensitiveBytes::from("aabc".as_bytes()).contains_lower_bytes("abc".as_bytes())
        );
        assert!(
            CaseInsensitiveBytes::from("aABC".as_bytes()).contains_lower_bytes("abc".as_bytes())
        );
        assert!(
            CaseInsensitiveBytes::from("aaBc".as_bytes()).contains_lower_bytes("abc".as_bytes())
        );
        assert!(
            CaseInsensitiveBytes::from("aabcd".as_bytes()).contains_lower_bytes("abc".as_bytes())
        );
        assert!(
            CaseInsensitiveBytes::from("aABCD".as_bytes()).contains_lower_bytes("abc".as_bytes())
        );

        assert!(!CaseInsensitiveBytes::from("".as_bytes()).contains_lower_bytes("abc".as_bytes()));
        assert!(!CaseInsensitiveBytes::from("a".as_bytes()).contains_lower_bytes("abc".as_bytes()));
        assert!(!CaseInsensitiveBytes::from("ab".as_bytes()).contains_lower_bytes("abc".as_bytes()));
        assert!(
            !CaseInsensitiveBytes::from("abd".as_bytes()).contains_lower_bytes("abc".as_bytes())
        );
        assert!(
            !CaseInsensitiveBytes::from("aab".as_bytes()).contains_lower_bytes("abc".as_bytes())
        );
        assert!(
            !CaseInsensitiveBytes::from("aaab".as_bytes()).contains_lower_bytes("abc".as_bytes())
        );
        assert!(
            !CaseInsensitiveBytes::from("aaaa".as_bytes()).contains_lower_bytes("abc".as_bytes())
        );
    }

    #[test]
    fn test_dequote() {
        for delimiter in ['\'', '"', '`'] {
            let input = format!("{}abc{}", delimiter, delimiter);
            assert_eq!(
                &MaybeQuotedBytes::from(input.as_bytes()).dequote(),
                b"abc",
                "input: {}",
                input
            );

            let input = format!("{}{}", delimiter, delimiter);
            assert_eq!(
                &MaybeQuotedBytes::from(input.as_bytes()).dequote(),
                b"",
                "input: {}",
                input
            );

            let input = format!("{}abc{}{}def{}", delimiter, delimiter, delimiter, delimiter);
            let output = format!("abc{}def", delimiter);
            assert_eq!(
                &MaybeQuotedBytes::from(input.as_bytes()).dequote(),
                output.as_bytes(),
                "input: {}",
                input
            );

            let input = format!("{}{}{}{}", delimiter, delimiter, delimiter, delimiter);
            let output = format!("{}", delimiter);
            assert_eq!(
                &MaybeQuotedBytes::from(input.as_bytes()).dequote(),
                output.as_bytes(),
                "input: {}",
                input
            );

            let input = format!(
                "{}{}{}{}{}{}",
                delimiter, delimiter, delimiter, delimiter, delimiter, delimiter
            );
            let output = format!("{}{}", delimiter, delimiter);
            assert_eq!(
                &MaybeQuotedBytes::from(input.as_bytes()).dequote(),
                output.as_bytes(),
                "input: {}",
                input
            );
        }

        assert_eq!(&MaybeQuotedBytes::from(b"abc".as_slice()).dequote(), b"abc");
        assert_eq!(&MaybeQuotedBytes::from(b"".as_slice()).dequote(), b"");
    }

    #[test]
    fn test_dequote_iter() {
        for delimiter in ['\'', '"', '`'] {
            let input = format!("{}abc{}", delimiter, delimiter);
            assert_eq!(
                MaybeQuotedBytes::from(input.as_bytes())
                    .dequote_iter()
                    .copied()
                    .collect::<Vec<_>>(),
                vec![b'a', b'b', b'c'],
                "input: {}",
                input
            );

            let input = format!("{}{}", delimiter, delimiter);
            assert_eq!(
                MaybeQuotedBytes::from(input.as_bytes())
                    .dequote_iter()
                    .collect::<Vec<_>>()
                    .len(),
                0,
                "input: {}",
                input
            );

            let input = format!("{}abc{}{}def{}", delimiter, delimiter, delimiter, delimiter);
            let output = format!("abc{}def", delimiter);
            assert_eq!(
                MaybeQuotedBytes::from(input.as_bytes())
                    .dequote_iter()
                    .copied()
                    .collect::<Vec<_>>(),
                output.as_bytes(),
                "input: {}",
                input
            );

            let input = format!("{}{}{}{}", delimiter, delimiter, delimiter, delimiter);
            let output = format!("{}", delimiter);
            assert_eq!(
                MaybeQuotedBytes::from(input.as_bytes())
                    .dequote_iter()
                    .copied()
                    .collect::<Vec<_>>(),
                output.as_bytes(),
                "input: {}",
                input
            );

            let input = format!(
                "{}{}{}{}{}{}",
                delimiter, delimiter, delimiter, delimiter, delimiter, delimiter
            );
            let output = format!("{}{}", delimiter, delimiter);
            assert_eq!(
                MaybeQuotedBytes::from(input.as_bytes())
                    .dequote_iter()
                    .copied()
                    .collect::<Vec<_>>(),
                output.as_bytes(),
                "input: {}",
                input
            );
        }

        assert_eq!(
            MaybeQuotedBytes::from(b"abc".as_slice())
                .dequote_iter()
                .copied()
                .collect::<Vec<_>>(),
            vec![b'a', b'b', b'c']
        );
        assert_eq!(
            MaybeQuotedBytes::from(b"".as_slice())
                .dequote_iter()
                .copied()
                .collect::<Vec<_>>()
                .len(),
            0
        );
    }

    #[test]
    fn test_hex_to_int() {
        let mut test_cases = Vec::new();
        for i in b'0'..=b'9' {
            test_cases.push((i, i - b'0'));
        }
        for a in b'a'..=b'f' {
            test_cases.push((a, a - b'a' + 10));
        }
        for a in b'A'..=b'F' {
            test_cases.push((a, a - b'A' + 10));
        }
        for (hex, int) in test_cases {
            assert_eq!(hex_to_int(hex), int, "hex: {}", hex as char);
        }
    }

    #[test]
    fn test_hexed_bytes() {
        let mut test_cases = Vec::new();
        for i in 0..=255 {
            test_cases.push((format!("{:02x}", i), i));
        }
        for (hex, int) in test_cases {
            assert_eq!(
                HexedBytes::from(hex.as_bytes()).decode(),
                vec![int],
                "hex: {}",
                hex
            );
        }

        assert_eq!(HexedBytes::from(b"".as_slice()).decode(), vec![]);
        assert_eq!(
            HexedBytes::from(b"0123456789abcdef".as_slice()).decode(),
            vec![0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef]
        );
    }
}
