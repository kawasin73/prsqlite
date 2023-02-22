const VARINT_FLAG_MASK: u8 = 0b1000_0000;
const VARINT_VAR_MASK: u8 = !VARINT_FLAG_MASK;

/// Parse varint
pub fn parse_varint(buf: &[u8]) -> (i64, usize) {
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
            let (result, consumed) = parse_varint(buf);
            assert_eq!(consumed, buf.len(), "buf: {:?}", buf);
            assert_eq!(result, v, "buf: {:?}", buf);
        }
    }

    #[test]
    fn test_parse_varint_consume() {
        let (_, consumed) = parse_varint(&[0, 0]);
        assert_eq!(consumed, 1);
        let (_, consumed) = parse_varint(&[129, 0, 0]);
        assert_eq!(consumed, 2);
        let (_, consumed) = parse_varint(&[255, 255, 255, 255, 255, 255, 255, 255, 255, 255]);
        assert_eq!(consumed, 9);
    }
}
