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

use std::fmt::Display;

use anyhow::{bail, Context};

use crate::cursor::BtreePayload;
use crate::utils::parse_varint;

// TODO: Own the buffer of Text and Blob.
#[derive(Debug, PartialEq)]
pub enum Value<'a> {
    Null,
    Integer(i64),
    Float(f64),
    Blob(&'a [u8]),
    Text(&'a str),
}

impl<'a> Display for Value<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Null => Ok(()),
            Value::Integer(i) => write!(f, "{i}"),
            Value::Float(d) => write!(f, "{d}"),
            Value::Blob(b) => write!(f, "{b:?}"),
            Value::Text(t) => write!(f, "{t}"),
        }
    }
}

pub struct SerialType(u32);

impl SerialType {
    pub fn content_size(&self) -> i32 {
        // TODO: use pre-calculated table for first 128 serial types.
        match self.0 {
            n if n <= 4 => n as i32,
            5 => 6,
            6 | 7 => 8,
            8 | 9 => 0,
            10 | 11 => {
                unimplemented!("reserved record is not implemented");
            }
            n => ((n - 12) >> 1) as i32,
        }
    }

    pub fn parse<'a>(&self, buf: &'a [u8]) -> anyhow::Result<Value<'a>> {
        if buf.len() < self.content_size() as usize {
            bail!(
                "buffer size {} is smaller than content size {}",
                buf.len(),
                self.content_size()
            );
        }
        let v = match self.0 {
            0 => Value::Null,
            1 => Value::Integer(i8::from_be_bytes(buf[..1].try_into().unwrap()) as i64),
            2 => Value::Integer(i16::from_be_bytes(buf[..2].try_into().unwrap()) as i64),
            // TODO: use std::mem::transmute.
            3 => Value::Integer(((buf[0] as i64) << 56 | (buf[1] as i64) << 48 | (buf[2] as i64) << 40) >> 40),
            4 => Value::Integer(i32::from_be_bytes(buf[..4].try_into().unwrap()) as i64),
            // TODO: use std::mem::transmute.
            5 => Value::Integer(
                ((buf[0] as i64) << 56
                    | (buf[1] as i64) << 48
                    | (buf[2] as i64) << 40
                    | (buf[3] as i64) << 32
                    | (buf[4] as i64) << 24
                    | (buf[5] as i64) << 16)
                    >> 16,
            ),
            6 => Value::Integer(i64::from_be_bytes(buf[..8].try_into().unwrap())),
            7 => Value::Float(f64::from_be_bytes(buf[..8].try_into().unwrap())),
            8 => Value::Integer(0),
            9 => Value::Integer(1),
            10 | 11 => {
                unimplemented!("reserved record is not implemented");
            }
            n => {
                let size = ((n - 12) >> 1) as usize;
                let buf = &buf[..size];
                if n & 1 == 0 {
                    Value::Blob(buf)
                } else {
                    Value::Text(std::str::from_utf8(buf).context("parse text")?)
                }
            }
        };
        Ok(v)
    }
}

/// Parse record header and return a list of serial types and content offsets.
///
/// TODO: support partial parsing.
pub fn parse_record_header(payload: &BtreePayload) -> anyhow::Result<Vec<(SerialType, i32)>> {
    let local_buf = payload.buf();
    let (header_size, consumed) = parse_varint(local_buf).context("parse record header size")?;
    let header_size: i32 = header_size.try_into().context("header size is too large")?;
    let mut header_offset = consumed as i32;
    let mut content_offset = header_size;

    let mut buf_loaded;
    let buf = if local_buf.len() > header_size as usize {
        buf_loaded = vec![0; header_size as usize];
        // SAFETY: buf_loaded does not overlap with payload.
        let n = unsafe { payload.load(0, &mut buf_loaded) }.context("load record header")?;
        if n != header_size as usize {
            bail!(
                "record header size {} does not match with loaded size {}",
                header_size,
                n
            );
        }
        &buf_loaded
    } else {
        local_buf
    };

    let mut parsed = Vec::new();
    while header_offset < header_size {
        let (serial_type, consumed) = parse_varint(&buf[header_offset as usize..]).context("parse serial type")?;
        let serial_type = SerialType(serial_type.try_into().context("serial type is too large")?);
        let content_size = serial_type.content_size();
        parsed.push((serial_type, content_offset));
        header_offset += consumed as i32;
        content_offset += content_size;
    }

    Ok(parsed)
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::cursor::BtreeCursor;
    use crate::test_utils::*;

    fn parse_record<'a>(payload: &BtreePayload, buf: &'a mut Vec<u8>) -> Vec<Value<'a>> {
        let headers = parse_record_header(payload).unwrap();
        assert_eq!(headers.len(), 4);
        *buf = vec![0; payload.size() as usize];
        let _ = unsafe { payload.load(0, buf).unwrap() };
        headers
            .iter()
            .map(|(serial_type, offset)| serial_type.parse(&buf[*offset as usize..]).unwrap())
            .collect()
    }

    #[test]
    fn test_parse_record() {
        let tables = ["CREATE TABLE example(col1, col2, col3, col4);"];
        const ONE: i64 = 1;
        let inserts = [
            "INSERT INTO example(col1, col2, col4) VALUES (null, true, false);".to_string(),
            format!(
                "INSERT INTO example(col1, col2, col3, col4) VALUES ({}, {}, {}, {});",
                i8::MAX,
                i8::MIN,
                i16::MAX,
                i16::MIN
            ),
            format!(
                "INSERT INTO example(col1, col2, col3, col4) VALUES ({}, {}, {}, {});",
                (ONE << 23) - 1,
                -(ONE << 23),
                i32::MAX,
                i32::MIN
            ),
            format!(
                "INSERT INTO example(col1, col2, col3, col4) VALUES ({}, {}, {}, {});",
                (ONE << 47) - 1,
                -(ONE << 47),
                i64::MAX,
                i64::MIN
            ),
            "INSERT INTO example(col1, col2, col3, col4) VALUES (0, 1, \"hello\", X'0123456789abcdef');".to_string(),
            "INSERT INTO example(col1) VALUES (0.5);".to_string(),
        ];
        let mut queries = Vec::new();
        queries.extend(tables);
        queries.extend(inserts.iter().map(|s| s.as_str()));
        let file = create_sqlite_database(&queries);
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let bctx = load_btree_context(file.as_file()).unwrap();
        let table_page_id = find_table_page_id("example", file.path());
        let mut buf = Vec::new();

        let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();
        cursor.move_to_first().unwrap();

        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let result = parse_record(&payload, &mut buf);
        assert_eq!(result[0], Value::Null);
        assert_eq!(result[1], Value::Integer(1));
        assert_eq!(result[2], Value::Null);
        assert_eq!(result[3], Value::Integer(0));
        drop(payload);

        cursor.next().unwrap();
        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let result = parse_record(&payload, &mut buf);
        assert_eq!(result[0], Value::Integer(i8::MAX as i64));
        assert_eq!(result[1], Value::Integer(i8::MIN as i64));
        assert_eq!(result[2], Value::Integer(i16::MAX as i64));
        assert_eq!(result[3], Value::Integer(i16::MIN as i64));
        drop(payload);

        cursor.next().unwrap();
        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let result = parse_record(&payload, &mut buf);
        assert_eq!(result[0], Value::Integer((ONE << 23) - 1));
        assert_eq!(result[1], Value::Integer(-(ONE << 23)));
        assert_eq!(result[2], Value::Integer(i32::MAX as i64));
        assert_eq!(result[3], Value::Integer(i32::MIN as i64));
        drop(payload);

        cursor.next().unwrap();
        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let result = parse_record(&payload, &mut buf);
        assert_eq!(result[0], Value::Integer((ONE << 47) - 1));
        assert_eq!(result[1], Value::Integer(-(ONE << 47)));
        assert_eq!(result[2], Value::Integer(i64::MAX));
        assert_eq!(result[3], Value::Integer(i64::MIN));
        drop(payload);

        cursor.next().unwrap();
        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let result = parse_record(&payload, &mut buf);
        assert_eq!(result[0], Value::Integer(0));
        assert_eq!(result[1], Value::Integer(1));
        assert_eq!(result[2], Value::Text("hello"));
        assert_eq!(
            result[3],
            Value::Blob(&[0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef])
        );
        drop(payload);

        cursor.next().unwrap();
        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let result = parse_record(&payload, &mut buf);
        assert_eq!(result[0], Value::Float(0.5));
    }
}
