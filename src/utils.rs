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

use std::cmp::Ordering;
use std::hash::Hash;
use std::hash::Hasher;

const VARINT_FLAG_MASK: u8 = 0b1000_0000;
const VARINT_VAR_MASK: u64 = (!VARINT_FLAG_MASK) as u64;

/// Convert u64 representation to i64.
///
/// For example: 0xffff_ffff_ffff_ffff -> -1
pub fn u64_to_i64(v: u64) -> i64 {
    i64::from_ne_bytes(v.to_ne_bytes())
}

/// Convert i64 to u64 representation.
///
/// For example: -1 -> 0xffff_ffff_ffff_ffff
pub fn i64_to_u64(v: i64) -> u64 {
    u64::from_ne_bytes(v.to_ne_bytes())
}

/// Parse varint.
///
/// Return None if the buffer is not valid varint.
pub fn parse_varint(buf: &[u8]) -> Option<(u64, usize)> {
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
pub fn unsafe_parse_varint(buf: &[u8]) -> (u64, usize) {
    assert!(!buf.is_empty());
    if buf[0] & VARINT_FLAG_MASK == 0 {
        (buf[0] as u64, 1)
    } else {
        let mut v = 0;
        for (i, v2) in buf.iter().enumerate().take(8) {
            v <<= 7;
            v |= *v2 as u64 & VARINT_VAR_MASK;
            if *v2 & VARINT_FLAG_MASK == 0 {
                return (v, i + 1);
            }
        }
        v <<= 8;
        v |= buf[8] as u64;
        (v, 9)
    }
}

/// Put varint into the `buf`.
///
/// Return the number of bytes written.
///
/// The `buf` must have at least 9 bytes.
pub fn put_varint(buf: &mut [u8], v: u64) -> usize {
    assert!(buf.len() >= 9);
    let mut v = v;
    if v & (0xff000000 << 32) != 0 {
        buf[8] = v as u8;
        v >>= 8;
        for v2 in buf[..8].iter_mut().rev() {
            *v2 = (v & 0x7f) as u8 | VARINT_FLAG_MASK;
            v >>= 7;
        }
        9
    } else {
        let mut reversed_buf = [0_u8; 9];
        let mut i = 0;
        loop {
            assert!(i < 9);
            reversed_buf[i] = (v & 0x7f) as u8 | VARINT_FLAG_MASK;
            v >>= 7;
            i += 1;
            if v == 0 {
                break;
            }
        }
        reversed_buf[0] &= VARINT_VAR_MASK as u8;
        for (v1, v2) in reversed_buf[..i].iter().rev().zip(buf.iter_mut()) {
            *v2 = *v1;
        }
        i
    }
}

/// Whether the byte is a space or not.
///
/// u8::is_ascii_whitespace() is not usable because it does not include b'\x0b'.
#[inline]
pub fn is_space(c: u8) -> bool {
    c == b' ' || (b'\t'..=b'\r').contains(&c)
}

const MAX_I64_PLUS_ONE: u64 = 9223372036854775808;

/// Result of parse_integer()
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ParseIntegerResult {
    /// Parsed integer
    Integer(i64),
    /// 9223372036854775808
    MaxPlusOne,
    /// Exceeds i64 range
    TooBig(bool),
    /// No digits
    Empty,
}

/// Parse integer literal.
///
/// This is inspired by `sqlite3Atoi64()` of SQLite.
///
/// This ignores leading and tailing spaces.
///
/// The first bool value returned indicates whether the input is valid or not.
/// Invalid inputs are:
///
/// * Contains non-digit characters
/// * Contains no digits
pub fn parse_integer(input: &[u8]) -> (bool, ParseIntegerResult) {
    let mut n = 0;

    // Skip leading spaces
    for byte in input.iter() {
        if !is_space(*byte) {
            break;
        }
        n += 1;
    }

    // Sign
    let positive = match input.get(n) {
        Some(b'-') => {
            n += 1;
            false
        }
        Some(b'+') => {
            n += 1;
            true
        }
        _ => true,
    };

    // Skip leading zeros
    let mut n_zero = 0;
    for byte in &input[n..] {
        if *byte != b'0' {
            break;
        }
        n_zero += 1;
    }

    // Parse digits
    let mut u = 0_u64;
    let mut digits = 0;
    for &byte in input[n + n_zero..].iter() {
        if byte.is_ascii_digit() {
            u = u.wrapping_mul(10).wrapping_add((byte - b'0') as u64);
            digits += 1;
        } else {
            break;
        }
    }

    // Extra non-digits at the tail
    let mut valid = true;
    for byte in &input[(n + n_zero + digits)..] {
        if !is_space(*byte) {
            valid = false;
            break;
        }
    }

    if n_zero + digits == 0 {
        (false, ParseIntegerResult::Empty)
    } else if digits < 19 {
        let v = if positive { u as i64 } else { -(u as i64) };
        (valid, ParseIntegerResult::Integer(v))
    } else if digits > 19 || u > MAX_I64_PLUS_ONE {
        (valid, ParseIntegerResult::TooBig(positive))
    } else if u == MAX_I64_PLUS_ONE {
        if positive {
            (valid, ParseIntegerResult::MaxPlusOne)
        } else {
            (valid, ParseIntegerResult::Integer(i64::MIN))
        }
    } else {
        assert!(u < MAX_I64_PLUS_ONE);
        let v = if positive { u as i64 } else { -(u as i64) };
        (valid, ParseIntegerResult::Integer(v))
    }
}

/// Parse float literal.
///
/// This is inspired by `sqlite3AtoF()` of SQLite.
///
/// This ignores leading and tailing spaces.
///
/// The input may:
///
/// * Contain '.'
/// * Contain 'e' or 'E'
/// * Overflow i64 range
pub fn parse_float(input: &[u8]) -> (bool, bool, f64) {
    let mut n = 0;
    let mut pure_integer = false;

    // Skip leading spaces
    for byte in input.iter() {
        if !is_space(*byte) {
            break;
        }
        n += 1;
    }

    // Sign
    let positive = match input.get(n) {
        Some(b'-') => {
            n += 1;
            false
        }
        Some(b'+') => {
            n += 1;
            true
        }
        _ => true,
    };

    // Skip leading zeros
    let mut n_zero = 0;
    for byte in &input[n..] {
        if *byte != b'0' {
            break;
        }
        n_zero += 1;
        pure_integer = true;
    }
    n += n_zero;

    let mut significand = 0;
    let mut dicimal_point: i64 = 0;
    let mut digits = 0;

    // Parse integer part
    for byte in &input[n..] {
        if byte.is_ascii_digit() {
            significand = significand * 10 + (byte - b'0') as i64;
            digits += 1;
            pure_integer = true;
            if significand < (i64::MAX - 9) / 10 {
                continue;
            }
        }
        break;
    }
    n += digits;
    for byte in &input[n..] {
        if byte.is_ascii_digit() {
            dicimal_point += 1;
            n += 1;
        } else {
            break;
        }
    }

    // Parse fractional part
    if let Some(&b'.') = input.get(n) {
        pure_integer = false;
        n += 1;
        let mut fractional_digits = 0;
        for byte in &input[n..] {
            if byte.is_ascii_digit() {
                if significand < (i64::MAX - 9) / 10 {
                    significand = significand * 10 + (byte - b'0') as i64;
                    dicimal_point -= 1;
                }
                fractional_digits += 1;
            } else {
                break;
            }
        }
        digits += fractional_digits;
        n += fractional_digits;
    }

    // Parse exponent part
    let mut valid = match input.get(n) {
        Some(b'e') | Some(b'E') => {
            n += 1;
            let exponent_sign = match input.get(n) {
                Some(b'+') => {
                    n += 1;
                    1
                }
                Some(b'-') => {
                    n += 1;
                    -1
                }
                _ => 1,
            };
            let mut exponent = 0;
            let mut valid_exponent = false;
            for byte in &input[n..] {
                if byte.is_ascii_digit() {
                    exponent = if exponent < 10000 {
                        exponent * 10 + (byte - b'0') as i32
                    } else {
                        10000
                    };
                    n += 1;
                    valid_exponent = true;
                } else {
                    break;
                }
            }
            dicimal_point += (exponent * exponent_sign) as i64;
            if valid_exponent {
                pure_integer = false;
            }
            valid_exponent
        }
        _ => true,
    };

    valid = valid && n_zero + digits > 0;

    // Skip leading spaces
    if valid {
        for byte in &input[n..] {
            if !is_space(*byte) {
                valid = false;
                break;
            }
        }
    }

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
    let v = match dicimal_point.try_into() {
        Ok(dicimal_point) => significand as f64 * 10.0f64.powi(dicimal_point),
        Err(_) => {
            if dicimal_point > 0 {
                f64::INFINITY
            } else {
                0.0
            }
        }
    };
    let v = if positive { v } else { -v };

    (valid, pure_integer, v)
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

impl PartialOrd for CaseInsensitiveBytes<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CaseInsensitiveBytes<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        for (a, b) in std::iter::zip(self.0, other.0) {
            let cmp = UPPER_TO_LOWER[*a as usize].cmp(&UPPER_TO_LOWER[*b as usize]);
            if cmp != Ordering::Equal {
                return cmp;
            }
        }
        self.0.len().cmp(&other.0.len())
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
                9223372036854775809,
            ),
            (&[255, 255, 255, 255, 255, 255, 255, 255, 255], u64::MAX),
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
    fn test_put_varint() {
        for v in [
            0,
            1,
            2,
            127,
            128,
            0b11_1111_0111_1111,
            0b1_1111_1011_1111_0111_1111,
            0b1111_1101_1111_1011_1111_0111_1111,
            0b1111_1101_1111_1011_1111_0111_1110_1111_1101_1111_1011_1111_0111_1111,
            9223372036854775809,
            u64::MAX,
        ] {
            let mut buf = [0; 10];
            let n = put_varint(buf.as_mut_slice(), v);

            let result = parse_varint(&buf[..n]);
            assert!(result.is_some(), "v: {v}, {:?}", &buf[..n]);
            let (v2, consumed) = result.unwrap();
            assert_eq!(v2, v);
            assert_eq!(consumed, n, "v: {v}");
        }
    }

    #[test]
    fn test_parse_integer() {
        let mut test_cases = Vec::new();
        for i in 0..=1000 {
            test_cases.push((i.to_string(), ParseIntegerResult::Integer(i)));
        }
        for (l, v) in [
            (" 12345 ", ParseIntegerResult::Integer(12345)),
            ("\t12345\t", ParseIntegerResult::Integer(12345)),
            ("\n12345\n", ParseIntegerResult::Integer(12345)),
            ("\x0b12345\x0b", ParseIntegerResult::Integer(12345)),
            ("\x0c12345\x0c", ParseIntegerResult::Integer(12345)),
            ("\r12345\r", ParseIntegerResult::Integer(12345)),
            ("   12345   ", ParseIntegerResult::Integer(12345)),
            ("   +12345   ", ParseIntegerResult::Integer(12345)),
            ("   -12345   ", ParseIntegerResult::Integer(-12345)),
            ("   +012345   ", ParseIntegerResult::Integer(12345)),
            ("   -012345   ", ParseIntegerResult::Integer(-12345)),
            ("0", ParseIntegerResult::Integer(0)),
            ("+0", ParseIntegerResult::Integer(0)),
            ("-0", ParseIntegerResult::Integer(0)),
            ("00", ParseIntegerResult::Integer(0)),
            ("00000000000000000000", ParseIntegerResult::Integer(0)),
            ("000000000000000000001", ParseIntegerResult::Integer(1)),
            (
                "9223372036854775807",
                ParseIntegerResult::Integer(9223372036854775807),
            ),
            (
                "09223372036854775807",
                ParseIntegerResult::Integer(9223372036854775807),
            ),
            (
                "-9223372036854775807",
                ParseIntegerResult::Integer(-9223372036854775807),
            ),
            ("9223372036854775808", ParseIntegerResult::MaxPlusOne),
            ("09223372036854775808", ParseIntegerResult::MaxPlusOne),
            (
                "-9223372036854775808",
                ParseIntegerResult::Integer(-9223372036854775808),
            ),
            ("9223372036854775809", ParseIntegerResult::TooBig(true)),
            ("-9223372036854775809", ParseIntegerResult::TooBig(false)),
            ("9999999999999999999", ParseIntegerResult::TooBig(true)),
            ("-9999999999999999999", ParseIntegerResult::TooBig(false)),
            ("99999999999999999999", ParseIntegerResult::TooBig(true)),
            ("-99999999999999999999", ParseIntegerResult::TooBig(false)),
            ("999999999999999999999", ParseIntegerResult::TooBig(true)),
            ("-999999999999999999999", ParseIntegerResult::TooBig(false)),
        ] {
            test_cases.push((l.to_string(), v));
        }
        for (mut literal, value) in test_cases {
            assert_eq!(
                parse_integer(literal.as_bytes()),
                (true, value),
                "literal: \"{}\"",
                literal
            );
            literal += "abc";
            assert_eq!(
                parse_integer(literal.as_bytes()),
                (false, value),
                "literal: \"{}\"",
                literal
            );
        }

        assert_eq!(parse_integer(b""), (false, ParseIntegerResult::Empty));
        assert_eq!(parse_integer(b" "), (false, ParseIntegerResult::Empty));
        assert_eq!(parse_integer(b"+"), (false, ParseIntegerResult::Empty));
        assert_eq!(parse_integer(b"-"), (false, ParseIntegerResult::Empty));
        assert_eq!(parse_integer(b"++10"), (false, ParseIntegerResult::Empty));
        assert_eq!(parse_integer(b"--10"), (false, ParseIntegerResult::Empty));
        assert_eq!(parse_integer(b"-+10"), (false, ParseIntegerResult::Empty));
        assert_eq!(parse_integer(b"a"), (false, ParseIntegerResult::Empty));
        assert_eq!(parse_integer(b"a123"), (false, ParseIntegerResult::Empty));
        assert_eq!(
            parse_integer(b"123.456"),
            (false, ParseIntegerResult::Integer(123))
        );
        assert_eq!(
            parse_integer(b"123e3"),
            (false, ParseIntegerResult::Integer(123))
        );
    }

    #[test]
    fn test_parse_float() {
        for (literal, value) in [
            (" 1.23 ", 1.23),
            ("\t1.23\t", 1.23),
            ("\n1.23\n", 1.23),
            ("\x0b1.23\x0b", 1.23),
            ("\x0c1.23\x0c", 1.23),
            ("\r1.23\r", 1.23),
            ("   1.23   ", 1.23),
            ("   +1.23   ", 1.23),
            ("   -1.23   ", -1.23),
            ("   +01.23   ", 1.23),
            ("   -01.23   ", -1.23),
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
            ("-1.23e5", -1.23e5),
            ("2e0123456789", f64::INFINITY),
            ("1e10000", f64::INFINITY),
            ("1e-10000", 0.0),
            ("922337203685477580.0", 922337203685477580.0),
            // "SELECT 922337203685477580.0e-10" show 92233720.3685478 in sqlite.
            ("922337203685477580.0e-10", 92233720.36854777),
        ] {
            assert_eq!(
                parse_float(literal.as_bytes()),
                (true, false, value),
                "literal: {}",
                literal
            );
            let with_extra = format!("{literal}abc");
            assert_eq!(
                parse_float(with_extra.as_bytes()),
                (false, false, value),
                "literal: {}",
                with_extra
            );
            let with_e = format!("{literal}e");
            assert_eq!(
                parse_float(with_e.as_bytes()),
                (false, false, value),
                "literal: {}",
                with_e
            );
        }
        assert_eq!(parse_float("1.23".as_bytes()), (true, false, 1.23));
        assert_eq!(parse_float("1.23e".as_bytes()), (false, false, 1.23));
        assert_eq!(parse_float("1.23e-".as_bytes()), (false, false, 1.23));
        assert_eq!(parse_float(".".as_bytes()), (false, false, 0.0));
        assert_eq!(parse_float("".as_bytes()), (false, false, 0.0));
        assert_eq!(parse_float(" ".as_bytes()), (false, false, 0.0));
        assert_eq!(parse_float("abc".as_bytes()), (false, false, 0.0));
        assert_eq!(parse_float("a1.23".as_bytes()), (false, false, 0.0));

        // Pure integer
        assert_eq!(parse_float("0".as_bytes()), (true, true, 0.0));
        assert_eq!(parse_float("123".as_bytes()), (true, true, 123.0));
        assert_eq!(
            parse_float("9223372036854775807".as_bytes()),
            (true, true, 9223372036854775808.0)
        );
        assert_eq!(
            parse_float("9223372036854775808".as_bytes()),
            (true, true, 9223372036854775808.0)
        );
        assert_eq!(
            parse_float("9999999999999999999".as_bytes()),
            (true, true, 9999999999999999999.0)
        );
        assert_eq!(
            parse_float("9223372036854775807a".as_bytes()),
            (false, true, 9223372036854775808.0)
        );
        assert_eq!(
            parse_float("9223372036854775807e".as_bytes()),
            (false, true, 9223372036854775808.0)
        );
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
    fn test_case_insensitive_bytes_cmp() {
        assert_eq!(
            CaseInsensitiveBytes::from(b"".as_slice())
                .cmp(&CaseInsensitiveBytes::from(b"".as_slice())),
            Ordering::Equal
        );
        assert_eq!(
            CaseInsensitiveBytes::from(b"abc".as_slice())
                .cmp(&CaseInsensitiveBytes::from(b"abc".as_slice())),
            Ordering::Equal
        );
        assert_eq!(
            CaseInsensitiveBytes::from(b"123.4".as_slice())
                .cmp(&CaseInsensitiveBytes::from(b"123.4".as_slice())),
            Ordering::Equal
        );
        assert_eq!(
            CaseInsensitiveBytes::from(b"abc".as_slice())
                .cmp(&CaseInsensitiveBytes::from(b"ABC".as_slice())),
            Ordering::Equal
        );
        assert_eq!(
            CaseInsensitiveBytes::from(b"abc".as_slice())
                .cmp(&CaseInsensitiveBytes::from(b"B".as_slice())),
            Ordering::Less
        );
        assert_eq!(
            CaseInsensitiveBytes::from(b"abc".as_slice())
                .cmp(&CaseInsensitiveBytes::from(b"B".as_slice())),
            Ordering::Less
        );
        assert_eq!(
            CaseInsensitiveBytes::from(b"bc".as_slice())
                .cmp(&CaseInsensitiveBytes::from(b"AB".as_slice())),
            Ordering::Greater
        );
        assert_eq!(
            CaseInsensitiveBytes::from(b"abcd".as_slice())
                .cmp(&CaseInsensitiveBytes::from(b"abc".as_slice())),
            Ordering::Greater
        );
        assert_eq!(
            CaseInsensitiveBytes::from(b"abcd".as_slice())
                .cmp(&CaseInsensitiveBytes::from(b"ABC".as_slice())),
            Ordering::Greater
        );
        assert_eq!(
            CaseInsensitiveBytes::from(b"abc".as_slice())
                .cmp(&CaseInsensitiveBytes::from(b"abcd".as_slice())),
            Ordering::Less
        );
        assert_eq!(
            CaseInsensitiveBytes::from(b"abc".as_slice())
                .cmp(&CaseInsensitiveBytes::from(b"ABCD".as_slice())),
            Ordering::Less
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
