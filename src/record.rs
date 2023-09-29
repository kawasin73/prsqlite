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

use anyhow::bail;
use anyhow::Context;

use crate::cursor::BtreePayload;
use crate::utils::len_varint;
use crate::utils::parse_varint;
use crate::utils::put_varint;
use crate::value::Buffer;
use crate::value::Value;
use crate::value::ValueCmp;

pub fn compare_record(keys: &[ValueCmp<'_>], payload: &BtreePayload) -> anyhow::Result<Ordering> {
    let mut record = parse_record(payload)?;
    if record.len() < keys.len() {
        bail!("keys is more than index columns");
    }
    for (i, key) in keys.iter().enumerate() {
        let index_value = record.get(i)?;
        match key.compare(&index_value) {
            Ordering::Equal => continue,
            o => return Ok(o),
        }
    }
    Ok(Ordering::Equal)
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
        let v = match self.0 {
            0 => Value::Null,
            1 => Value::Integer(i8::from_be_bytes(buf[..1].try_into()?) as i64),
            2 => Value::Integer(i16::from_be_bytes(buf[..2].try_into()?) as i64),
            // TODO: use std::mem::transmute.
            3 => {
                if buf.len() < 3 {
                    bail!("buffer size {} does not match integer 3", buf.len());
                }
                Value::Integer(
                    ((buf[0] as i64) << 56 | (buf[1] as i64) << 48 | (buf[2] as i64) << 40) >> 40,
                )
            }
            4 => Value::Integer(i32::from_be_bytes(buf[..4].try_into()?) as i64),
            // TODO: use std::mem::transmute.
            5 => {
                if buf.len() < 6 {
                    bail!("buffer size {} does not match integer 6", buf.len());
                }
                Value::Integer(
                    ((buf[0] as i64) << 56
                        | (buf[1] as i64) << 48
                        | (buf[2] as i64) << 40
                        | (buf[3] as i64) << 32
                        | (buf[4] as i64) << 24
                        | (buf[5] as i64) << 16)
                        >> 16,
                )
            }
            6 => Value::Integer(i64::from_be_bytes(buf[..8].try_into()?)),
            7 => {
                let f = f64::from_be_bytes(buf[..8].try_into()?);
                if f.is_nan() {
                    Value::Null
                } else {
                    Value::Real(f)
                }
            }
            8 => Value::Integer(0),
            9 => Value::Integer(1),
            10 | 11 => {
                bail!("reserved record is not implemented");
            }
            n => {
                let size = ((n - 12) >> 1) as usize;
                if buf.len() < size {
                    bail!(
                        "buffer size {} is smaller than content size {}",
                        buf.len(),
                        size
                    );
                }
                let buf = &buf[..size];
                if n & 1 == 0 {
                    Value::Blob(Buffer::Ref(buf))
                } else {
                    Value::Text(Buffer::Ref(buf))
                }
            }
        };
        Ok(v)
    }
}

pub trait RecordPayload {
    fn size(&self) -> i32;
    fn buf(&self) -> &[u8];
    fn load(&self, offset: i32, buf: &mut [u8]) -> anyhow::Result<usize>;
}

/// A wrapper of BtreePayload to implement RecordPayload.
///
/// TODO: This abstraction was introduced for FakePayload in tests. Consider
/// better abstraction.
pub struct BtreeRecordPayload<'a>(&'a BtreePayload<'a>);

impl RecordPayload for BtreeRecordPayload<'_> {
    #[inline]
    fn size(&self) -> i32 {
        self.0.size()
    }

    #[inline]
    fn buf(&self) -> &[u8] {
        self.0.buf()
    }

    #[inline]
    fn load(&self, offset: i32, buf: &mut [u8]) -> anyhow::Result<usize> {
        self.0.load(offset, buf)
    }
}

impl<'a> From<&'a BtreePayload<'a>> for BtreeRecordPayload<'a> {
    fn from(payload: &'a BtreePayload<'a>) -> Self {
        Self(payload)
    }
}

pub struct Record<P: RecordPayload> {
    payload: P,
    header: Vec<(SerialType, i32)>,
    tmp_buf: Vec<u8>,
}

#[inline]
pub fn parse_record<'a>(
    payload: &'a BtreePayload<'a>,
) -> anyhow::Result<Record<BtreeRecordPayload<'a>>> {
    Record::parse(payload.into())
}

impl<P: RecordPayload> Record<P> {
    pub fn parse(payload: P) -> anyhow::Result<Self> {
        let header = parse_record_header_payload(&payload)?;
        Ok(Self {
            payload,
            header,
            tmp_buf: Vec::new(),
        })
    }

    pub fn len(&self) -> usize {
        self.header.len()
    }

    pub fn get(&mut self, i: usize) -> anyhow::Result<Value<'_>> {
        let Some((serial_type, offset)) = &self.header.get(i) else {
            bail!("index out of range");
        };
        let offset = *offset;
        let content_size = serial_type.content_size() as usize;
        let buf = if offset as usize + content_size > self.payload.buf().len() {
            self.tmp_buf.resize(content_size, 0);
            let n = self.payload.load(offset, &mut self.tmp_buf)?;
            if n != content_size {
                bail!("failed to load rowid from index payload");
            }
            &self.tmp_buf
        } else {
            &self.payload.buf()[offset as usize..offset as usize + content_size]
        };
        serial_type.parse(buf)
    }
}

#[inline]
pub fn parse_record_header(payload: &BtreePayload) -> anyhow::Result<Vec<(SerialType, i32)>> {
    parse_record_header_payload::<BtreeRecordPayload>(&payload.into())
}

/// Parse record header and return a list of serial types and content offsets.
///
/// TODO: support partial parsing.
fn parse_record_header_payload<P: RecordPayload>(
    payload: &P,
) -> anyhow::Result<Vec<(SerialType, i32)>> {
    let local_buf = payload.buf();
    let (header_size, consumed) = parse_varint(local_buf).context("parse record header size")?;
    let header_size: i32 = header_size.try_into().context("header size is too large")?;
    let mut header_offset = consumed as i32;
    let mut content_offset = header_size;

    let mut buf_loaded;
    let buf = if local_buf.len() > header_size as usize {
        buf_loaded = vec![0; header_size as usize];
        let n = payload
            .load(0, &mut buf_loaded)
            .context("load record header")?;
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
        let (serial_type, consumed) =
            parse_varint(&buf[header_offset as usize..]).context("parse serial type")?;
        let serial_type = SerialType(serial_type.try_into().context("serial type is too large")?);
        let content_size = serial_type.content_size();
        parsed.push((serial_type, content_offset));
        header_offset += consumed as i32;
        content_offset += content_size;
    }

    Ok(parsed)
}

/// Serialize record.
///
/// The logic mainly comes from `OP_MakeRecord` in `vdbe.c`.
///
/// TODO: Consider reduce memory copy. The returned temporary Vec<u8> is not
/// necessary?
pub fn build_record(record: &[Value<'_>]) -> Vec<u8> {
    // TODO: How to avoid Vec allocation?
    let mut values = Vec::with_capacity(record.len());
    let mut header_size = 0;
    let mut data_size = 0;
    for value in record {
        let serial_type = match value {
            Value::Null => {
                header_size += 1;
                0
            }
            Value::Integer(i) => {
                let u = if *i < 0 { (!*i) as u64 } else { *i as u64 };
                header_size += 1;
                if u <= 127 {
                    if (*i & 1) == *i {
                        // u is 0 or 1.
                        8 + u as u32
                    } else {
                        data_size += 1;
                        1
                    }
                } else if u <= 32767 {
                    data_size += 2;
                    2
                } else if u <= 8388607 {
                    data_size += 3;
                    3
                } else if u <= 2147483647 {
                    data_size += 4;
                    4
                } else if u <= 140737488355327 {
                    data_size += 6;
                    5
                } else {
                    data_size += 8;
                    6
                }
            }
            Value::Real(_) => {
                header_size += 1;
                data_size += 8;
                7
            }
            Value::Text(buf) | Value::Blob(buf) => {
                let serial_type =
                    (buf.len() << 1) + 12 + (matches!(value, Value::Text(_)) as usize);
                // TODO: how to guarantee serial_type <= u32::MAX?
                assert!(serial_type <= u32::MAX as usize);
                let serial_type = serial_type as u32;
                header_size += len_varint(serial_type as u64);
                data_size += buf.len();
                serial_type
            }
        };
        values.push((SerialType(serial_type), value));
    }
    if header_size <= 126 {
        // The header size is usually less than 126.
        header_size += 1;
    } else {
        let len_varint_header_size = len_varint(header_size as u64);
        header_size += len_varint_header_size;
        if len_varint_header_size != len_varint(header_size as u64) {
            header_size += 1;
        }
    }
    let size = header_size + data_size;

    let mut buf = vec![0; size];
    let mut i_header = put_varint(&mut buf, header_size as u64);
    let mut i_data = header_size;
    for (serial_type, value) in values {
        // TODO: Consider how to reduce conditional branches.
        if serial_type.0 <= 127 {
            buf[i_header] = serial_type.0 as u8;
            i_header += 1;
        } else {
            let n = put_varint(&mut buf[i_header..], serial_type.0 as u64);
            i_header += n;
        }
        match serial_type.0 {
            0 | 8 | 9 => {}
            st if st <= 6 => {
                // TODO: Confirm the unreachable has no overhead.
                let Value::Integer(i) = value else {
                    unreachable!("serial type 1 ~ 6 must be Value::Integer");
                };
                let mut i = *i;
                let n = serial_type.content_size() as usize;
                assert!(i_data + n <= buf.len());
                for p in buf[i_data..i_data + n].iter_mut().rev() {
                    *p = (i & 0xFF) as u8;
                    i >>= 8;
                }
                i_data += n;
            }
            7 => {
                let Value::Real(d) = value else {
                    unreachable!("serial type 7 must be Value::Real");
                };
                buf[i_data..i_data + 8].copy_from_slice(&d.to_be_bytes());
                i_data += 8;
            }
            _ => {
                let data = match value {
                    Value::Text(buf) | Value::Blob(buf) => buf,
                    _ => unreachable!("serial type must be Value::Text or Value::Blob"),
                };
                buf[i_data..i_data + data.len()].copy_from_slice(data);
                i_data += data.len();
            }
        }
    }
    assert_eq!(i_header, header_size);
    assert_eq!(i_data, size);
    buf
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::cursor::BtreeCursor;
    use crate::test_utils::*;

    const ONE: i64 = 1;

    #[test]
    fn test_parse_record() {
        let tables = ["CREATE TABLE example(col1, col2, col3, col4);"];
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

        let mut cursor = BtreeCursor::new(table_page_id, &pager, &bctx).unwrap();
        cursor.move_to_first().unwrap();

        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let mut record = parse_record(&payload).unwrap();
        assert_eq!(record.get(0).unwrap(), Value::Null);
        assert_eq!(record.get(1).unwrap(), Value::Integer(1));
        assert_eq!(record.get(2).unwrap(), Value::Null);
        assert_eq!(record.get(3).unwrap(), Value::Integer(0));
        drop(payload);

        cursor.move_next().unwrap();
        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let mut record = parse_record(&payload).unwrap();
        assert_eq!(record.get(0).unwrap(), Value::Integer(i8::MAX as i64));
        assert_eq!(record.get(1).unwrap(), Value::Integer(i8::MIN as i64));
        assert_eq!(record.get(2).unwrap(), Value::Integer(i16::MAX as i64));
        assert_eq!(record.get(3).unwrap(), Value::Integer(i16::MIN as i64));
        drop(payload);

        cursor.move_next().unwrap();
        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let mut record = parse_record(&payload).unwrap();
        assert_eq!(record.get(0).unwrap(), Value::Integer((ONE << 23) - 1));
        assert_eq!(record.get(1).unwrap(), Value::Integer(-(ONE << 23)));
        assert_eq!(record.get(2).unwrap(), Value::Integer(i32::MAX as i64));
        assert_eq!(record.get(3).unwrap(), Value::Integer(i32::MIN as i64));
        drop(payload);

        cursor.move_next().unwrap();
        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let mut record = parse_record(&payload).unwrap();
        assert_eq!(record.get(0).unwrap(), Value::Integer((ONE << 47) - 1));
        assert_eq!(record.get(1).unwrap(), Value::Integer(-(ONE << 47)));
        assert_eq!(record.get(2).unwrap(), Value::Integer(i64::MAX));
        assert_eq!(record.get(3).unwrap(), Value::Integer(i64::MIN));
        drop(payload);

        cursor.move_next().unwrap();
        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let mut record = parse_record(&payload).unwrap();
        assert_eq!(record.get(0).unwrap(), Value::Integer(0));
        assert_eq!(record.get(1).unwrap(), Value::Integer(1));
        assert_eq!(
            record.get(2).unwrap(),
            Value::Text(b"hello".as_slice().into())
        );
        assert_eq!(
            record.get(3).unwrap(),
            Value::Blob(
                [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef]
                    .as_slice()
                    .into()
            )
        );
        drop(payload);

        cursor.move_next().unwrap();
        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let mut record = parse_record(&payload).unwrap();
        assert_eq!(record.get(0).unwrap(), Value::Real(0.5));
    }

    #[test]
    fn test_parse_real() {
        assert_eq!(
            SerialType(7).parse(0_f64.to_be_bytes().as_slice()).unwrap(),
            Value::Real(0.0)
        );
        assert_eq!(
            SerialType(7)
                .parse(1.1_f64.to_be_bytes().as_slice())
                .unwrap(),
            Value::Real(1.1)
        );
        // NaN
        assert_eq!(
            SerialType(7)
                .parse(f64::NAN.to_be_bytes().as_slice())
                .unwrap(),
            Value::Null
        );
    }

    struct FakePayload<'a> {
        buf: &'a [u8],
    }

    impl RecordPayload for FakePayload<'_> {
        fn size(&self) -> i32 {
            self.buf.len() as i32
        }

        fn buf(&self) -> &[u8] {
            self.buf
        }

        fn load(&self, offset: i32, buf: &mut [u8]) -> anyhow::Result<usize> {
            let n = buf.len().min(self.buf.len() - offset as usize);
            buf[..n].copy_from_slice(&self.buf[offset as usize..offset as usize + n]);
            Ok(n)
        }
    }

    #[test]
    fn test_build_record() {
        let values = vec![
            Value::Null,
            Value::Integer(0),
            Value::Integer(-1),
            Value::Integer(1),
            Value::Integer(2),
            Value::Integer(i8::MIN as i64),
            Value::Integer(i8::MAX as i64),
            Value::Integer(i16::MIN as i64),
            Value::Integer(i16::MAX as i64),
            Value::Integer((ONE << 23) - 1),
            Value::Integer(-(ONE << 23)),
            Value::Integer(i32::MIN as i64),
            Value::Integer(i32::MAX as i64),
            Value::Integer((ONE << 47) - 1),
            Value::Integer(-(ONE << 47)),
            Value::Integer(i64::MIN),
            Value::Integer(i64::MAX),
            Value::Real(0.0),
            Value::Real(12345.6),
            Value::Text(Buffer::Owned(b"hello".to_vec())),
            Value::Blob(Buffer::Owned(b"world".to_vec())),
        ];
        let buf = build_record(&values);
        let mut record = Record::parse(FakePayload { buf: &buf }).unwrap();
        for (i, value) in values.iter().enumerate() {
            assert_eq!(record.get(i).unwrap(), *value, "index {}", i);
        }

        // No data but header only.
        assert_eq!(build_record(&[Value::Null]), vec![2, 0]);
        let buf = build_record(&vec![Value::Null; 126]);
        assert_eq!(buf[0], 127);
        assert_eq!(&buf[1..], &[0; 126]);
        assert_eq!(Record::parse(FakePayload { buf: &buf }).unwrap().len(), 126);
        let buf = build_record(&vec![Value::Null; 127]);
        assert_eq!(&buf[..2], &[129, 1]);
        assert_eq!(&buf[2..], &[0; 127]);
        assert_eq!(Record::parse(FakePayload { buf: &buf }).unwrap().len(), 127);
        let buf = build_record(&vec![Value::Null; 128]);
        assert_eq!(&buf[..2], &[129, 2]);
        assert_eq!(&buf[2..], &[0; 128]);
        assert_eq!(Record::parse(FakePayload { buf: &buf }).unwrap().len(), 128);

        // Multi byte header (text).
        let buf = build_record(&[Value::Text(Buffer::Owned(vec![0; 58]))]);
        assert_eq!(buf[..3], vec![3, 129, 1]);
        assert_eq!(buf.len() - 3, 58);
        let mut record = Record::parse(FakePayload { buf: &buf }).unwrap();
        assert_eq!(
            record.get(0).unwrap(),
            Value::Text(Buffer::Owned(vec![0; 58]))
        );

        // Multi byte header (blob).
        let buf = build_record(&[Value::Blob(Buffer::Owned(vec![0; 58]))]);
        assert_eq!(buf[..3], vec![3, 129, 0]);
        assert_eq!(buf.len() - 3, 58);
        let mut record = Record::parse(FakePayload { buf: &buf }).unwrap();
        assert_eq!(
            record.get(0).unwrap(),
            Value::Blob(Buffer::Owned(vec![0; 58]))
        );
    }
}
