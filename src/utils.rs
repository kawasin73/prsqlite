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

/// Converts a single byte to its uppercase equivalent.
///
/// This only support ascii characters conversion (i.e. 0 ~ 127).
pub static UPPER_TO_LOWER: [u8; 256] = [
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, // 0x00 - 0x0F
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, // 0x10 - 0x1F
    0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, // 0x20 - 0x2F
    0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, // 0x30 - 0x3F
    0x40, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, // 0x40 - 0x4F
    0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F, // 0x50 - 0x5F
    0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, // 0x60 - 0x6F
    0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x7F, // 0x70 - 0x7F
    0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8A, 0x8B, 0x8C, 0x8D, 0x8E, 0x8F, // 0x80 - 0x8F
    0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9A, 0x9B, 0x9C, 0x9D, 0x9E, 0x9F, // 0x90 - 0x9F
    0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6, 0xA7, 0xA8, 0xA9, 0xAA, 0xAB, 0xAC, 0xAD, 0xAE, 0xAF, // 0xA0 - 0xAF
    0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8, 0xB9, 0xBA, 0xBB, 0xBC, 0xBD, 0xBE, 0xBF, // 0xB0 - 0xBF
    0xC0, 0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7, 0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF, // 0xC0 - 0xCF
    0xD0, 0xD1, 0xD2, 0xD3, 0xD4, 0xD5, 0xD6, 0xD7, 0xD8, 0xD9, 0xDA, 0xDB, 0xDC, 0xDD, 0xDE, 0xDF, // 0xD0 - 0xDF
    0xE0, 0xE1, 0xE2, 0xE3, 0xE4, 0xE5, 0xE6, 0xE7, 0xE8, 0xE9, 0xEA, 0xEB, 0xEC, 0xED, 0xEE, 0xEF, // 0xE0 - 0xEF
    0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6, 0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF, // 0xF0 - 0xFF
];

pub fn upper_to_lower(buf: &mut [u8]) {
    for b in buf {
        *b = UPPER_TO_LOWER[*b as usize];
    }
}

/// A wrapper for bytes to compare each other case insensitively with zero allocation.
#[derive(Eq)]
pub struct UpperToLowerBytes<'a>(&'a [u8]);

impl UpperToLowerBytes<'_> {
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
}

impl<'a> From<&'a [u8]> for UpperToLowerBytes<'a> {
    fn from(bytes: &'a [u8]) -> Self {
        UpperToLowerBytes(bytes)
    }
}

impl PartialEq for UpperToLowerBytes<'_> {
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
            (&[192, 128, 128, 128, 128, 128, 128, 128, 1], -9223372036854775807),
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
        let (_, consumed) = unsafe_parse_varint(&[255, 255, 255, 255, 255, 255, 255, 255, 255, 255]);
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
    fn test_upper_to_lower_table() {
        for c in b'A'..=b'Z' {
            assert_eq!(UPPER_TO_LOWER[c as usize], c + (b'a' - b'A'));
        }
        for c in u8::MIN..=u8::MAX {
            if (b'A'..=b'Z').contains(&c) {
                continue;
            }
            assert_eq!(UPPER_TO_LOWER[c as usize], c);
        }
    }

    #[test]
    fn test_upper_to_lower_bytes() {
        assert!(UpperToLowerBytes::from("".as_bytes()) == (UpperToLowerBytes::from("".as_bytes())));
        assert!(UpperToLowerBytes::from("abc".as_bytes()) != (UpperToLowerBytes::from("abcd".as_bytes())));
        assert!(UpperToLowerBytes::from("abc".as_bytes()) == (UpperToLowerBytes::from("abc".as_bytes())));
        assert!(UpperToLowerBytes::from("ABc".as_bytes()) == (UpperToLowerBytes::from("aBC".as_bytes())));
        assert!(UpperToLowerBytes::from("abc".as_bytes()) != (UpperToLowerBytes::from("abd".as_bytes())));
    }

    #[test]
    fn test_equal_to_lower_bytes() {
        assert!(UpperToLowerBytes::from("".as_bytes()).equal_to_lower_bytes("".as_bytes()));
        assert!(!UpperToLowerBytes::from("abc".as_bytes()).equal_to_lower_bytes("abcd".as_bytes()));
        assert!(UpperToLowerBytes::from("abc".as_bytes()).equal_to_lower_bytes("abc".as_bytes()));
        assert!(UpperToLowerBytes::from("ABC".as_bytes()).equal_to_lower_bytes("abc".as_bytes()));
        assert!(UpperToLowerBytes::from("AbC".as_bytes()).equal_to_lower_bytes("abc".as_bytes()));
        // If the other part is not lower case, it always returns false.
        assert!(!UpperToLowerBytes::from("abc".as_bytes()).equal_to_lower_bytes("Abc".as_bytes()));
    }
}
