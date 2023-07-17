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
        if count == 9 {
            return true;
        } else if b & VARINT_FLAG_MASK == 0 {
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
            assert_eq!(consumed, buf.len(), "buf: {:?}", buf);
            assert_eq!(result, v, "buf: {:?}", buf);

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
}
