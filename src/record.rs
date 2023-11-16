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
use std::fmt::Debug;
use std::marker::PhantomData;

use anyhow::bail;
use anyhow::Context;

use crate::cursor::BtreePayload;
use crate::payload::LocalPayload;
use crate::payload::Payload;
use crate::payload::PayloadSize;
use crate::utils::len_varint;
use crate::utils::parse_varint;
use crate::utils::put_varint;
use crate::value::Buffer;
use crate::value::Value;
use crate::value::ValueCmp;

pub fn compare_record(
    comparators: &[Option<ValueCmp<'_>>],
    payload: &BtreePayload,
) -> anyhow::Result<Ordering> {
    let mut record = parse_record(payload)?;
    if record.len() < comparators.len() {
        bail!("keys is more than index columns");
    }
    for (i, cmp) in comparators.iter().enumerate() {
        let index_value = record.get(i)?;
        match (cmp, index_value) {
            (None, None) => continue,
            (None, Some(_)) => return Ok(Ordering::Less),
            (Some(_), None) => return Ok(Ordering::Greater),
            (Some(cmp), Some(index_value)) => match cmp.compare(&index_value) {
                Ordering::Equal => continue,
                o => return Ok(o),
            },
        }
    }
    Ok(Ordering::Equal)
}

pub struct SerialType(u32);

impl SerialType {
    pub fn content_size(&self) -> u32 {
        // TODO: use pre-calculated table for first 128 serial types.
        match self.0 {
            n if n <= 4 => n,
            5 => 6,
            6 | 7 => 8,
            8 | 9 => 0,
            10 | 11 => {
                unimplemented!("reserved record is not implemented");
            }
            n => (n - 12) >> 1,
        }
    }

    pub fn parse<'a>(&self, buf: &'a [u8]) -> anyhow::Result<Option<Value<'a>>> {
        let v = match self.0 {
            0 => None,
            1 => Some(Value::Integer(
                i8::from_be_bytes(buf[..1].try_into()?) as i64
            )),
            2 => Some(Value::Integer(
                i16::from_be_bytes(buf[..2].try_into()?) as i64
            )),
            // TODO: use std::mem::transmute.
            3 => {
                if buf.len() < 3 {
                    bail!("buffer size {} does not match integer 3", buf.len());
                }
                Some(Value::Integer(
                    ((buf[0] as i64) << 56 | (buf[1] as i64) << 48 | (buf[2] as i64) << 40) >> 40,
                ))
            }
            4 => Some(Value::Integer(
                i32::from_be_bytes(buf[..4].try_into()?) as i64
            )),
            // TODO: use std::mem::transmute.
            5 => {
                if buf.len() < 6 {
                    bail!("buffer size {} does not match integer 6", buf.len());
                }
                Some(Value::Integer(
                    ((buf[0] as i64) << 56
                        | (buf[1] as i64) << 48
                        | (buf[2] as i64) << 40
                        | (buf[3] as i64) << 32
                        | (buf[4] as i64) << 24
                        | (buf[5] as i64) << 16)
                        >> 16,
                ))
            }
            6 => Some(Value::Integer(i64::from_be_bytes(buf[..8].try_into()?))),
            7 => {
                let f = f64::from_be_bytes(buf[..8].try_into()?);
                if f.is_nan() {
                    None
                } else {
                    Some(Value::Real(f))
                }
            }
            8 => Some(Value::Integer(0)),
            9 => Some(Value::Integer(1)),
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
                let v = if n & 1 == 0 {
                    Value::Blob(Buffer::Ref(buf))
                } else {
                    Value::Text(Buffer::Ref(buf))
                };
                Some(v)
            }
        };
        Ok(v)
    }
}

pub struct Record<'a, P: LocalPayload<E>, E> {
    payload: &'a P,
    header: Vec<(SerialType, usize)>,
    tmp_buf: Vec<u8>,
    error_type: PhantomData<E>,
}

#[inline]
pub fn parse_record<'a>(
    payload: &'a BtreePayload<'a>,
) -> anyhow::Result<Record<BtreePayload<'a>, crate::cursor::Error>> {
    Record::parse(payload)
}

impl<'a, P: LocalPayload<E>, E: Debug> Record<'a, P, E> {
    pub fn parse(payload: &'a P) -> anyhow::Result<Self> {
        let header = parse_record_header_payload(payload)?;
        Ok(Self {
            payload,
            header,
            tmp_buf: Vec::new(),
            error_type: PhantomData,
        })
    }

    pub fn len(&self) -> usize {
        self.header.len()
    }

    pub fn get(&mut self, i: usize) -> anyhow::Result<Option<Value<'_>>> {
        let Some((serial_type, offset)) = &self.header.get(i) else {
            bail!("index out of range");
        };
        let offset = *offset;
        let content_size = serial_type.content_size() as usize;
        let buf = if content_size == 0 {
            // Workaround because if offset is the tail, self.payload.load() fails.
            &[]
        } else if offset + content_size > self.payload.buf().len() {
            self.tmp_buf.resize(content_size, 0);
            let n = self
                .payload
                .load(offset, &mut self.tmp_buf)
                .map_err(|e| anyhow::anyhow!("payload load: {:?}", e))?;
            if n != content_size {
                bail!("failed to load rowid from index payload");
            }
            &self.tmp_buf
        } else {
            &self.payload.buf()[offset..offset + content_size]
        };
        serial_type.parse(buf)
    }
}

#[inline]
pub fn parse_record_header(payload: &BtreePayload) -> anyhow::Result<Vec<(SerialType, usize)>> {
    parse_record_header_payload::<BtreePayload, crate::cursor::Error>(payload)
}

/// Parse record header and return a list of serial types and content offsets.
///
/// TODO: support partial parsing.
fn parse_record_header_payload<P: LocalPayload<E>, E: Debug>(
    payload: &P,
) -> anyhow::Result<Vec<(SerialType, usize)>> {
    let local_buf = payload.buf();
    let (header_size, consumed) = parse_varint(local_buf).context("parse record header size")?;
    let header_size: usize = header_size.try_into().context("header size is too large")?;
    let mut header_offset = consumed;
    let mut content_offset = header_size;

    let mut buf_loaded;
    let buf = if local_buf.len() > header_size {
        buf_loaded = vec![0; header_size];
        let n = payload
            .load(0, &mut buf_loaded)
            .map_err(|e| anyhow::anyhow!("load record header: {:?}", e))?;
        if n != header_size {
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
            parse_varint(&buf[header_offset..]).context("parse serial type")?;
        let serial_type = SerialType(serial_type.try_into().context("serial type is too large")?);
        let content_size = serial_type.content_size();
        parsed.push((serial_type, content_offset));
        header_offset += consumed;
        content_offset += content_size as usize;
    }

    Ok(parsed)
}

/// Serialize record.
///
/// The logic mainly comes from `OP_MakeRecord` in `vdbe.c`.
pub struct RecordPayload<'a> {
    values: Vec<(SerialType, Option<&'a Value<'a>>)>,
    header_size: usize,
    payload_size: PayloadSize,
}

impl<'a> RecordPayload<'a> {
    pub fn new(record: &'a [Option<&'a Value<'a>>]) -> anyhow::Result<Self> {
        let mut values = Vec::with_capacity(record.len());
        let mut header_size = 0;
        let mut data_size = 0;
        for value in record {
            let serial_type = match value {
                None => {
                    header_size += 1;
                    0
                }
                Some(Value::Integer(i)) => {
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
                Some(Value::Real(_)) => {
                    header_size += 1;
                    data_size += 8;
                    7
                }
                Some(Value::Text(buf)) | Some(Value::Blob(buf)) => {
                    let serial_type =
                        (buf.len() << 1) + 12 + (matches!(value, Some(Value::Text(_))) as usize);
                    // TODO: how to guarantee serial_type <= u32::MAX?
                    assert!(serial_type <= u32::MAX as usize);
                    let serial_type = serial_type as u32;
                    header_size += len_varint(serial_type as u64);
                    data_size += buf.len();
                    serial_type
                }
            };
            values.push((SerialType(serial_type), *value));
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
        let payload_size: PayloadSize = ((header_size + data_size) as u64)
            .try_into()
            .map_err(|_| anyhow::anyhow!("payload size too large"))?;

        Ok(Self {
            values,
            header_size,
            payload_size,
        })
    }
}

impl Payload<()> for RecordPayload<'_> {
    fn size(&self) -> PayloadSize {
        self.payload_size
    }

    /// Copy the record payload to the buffer.
    ///
    /// # Arguments
    ///
    /// * `offset` - The offset of the payload to copy. This must be either 0 or
    ///   larger than 9.
    /// * `buf` - The buffer to copy the payload. This must be larger than 9
    ///   bytes.
    fn load(&self, offset: usize, buf: &mut [u8]) -> std::result::Result<usize, ()> {
        if offset == 0 && buf.len() >= self.header_size {
            // Optimized path: most case is buf.len() <= self.header_size. Copy the header
            // with less conditional branches than below.
            let mut i_header = put_varint(buf, self.header_size as u64);
            for (serial_type, _) in self.values.iter() {
                if serial_type.0 <= 127 {
                    buf[i_header] = serial_type.0 as u8;
                    i_header += 1;
                } else {
                    let n = put_varint(&mut buf[i_header..], serial_type.0 as u64);
                    i_header += n;
                }
            }
            assert_eq!(i_header, self.header_size);
        } else if offset < self.header_size {
            let mut i_header = if offset == 0 {
                assert!(buf.len() >= 9 || buf.len() >= self.header_size);
                put_varint(buf, self.header_size as u64)
            } else {
                assert!(offset >= 9);
                len_varint(self.header_size as u64)
            };
            for (serial_type, _) in self.values.iter() {
                let n = len_varint(serial_type.0 as u64);
                if i_header >= offset {
                    let offset_in_buf = i_header - offset;
                    if n + offset_in_buf >= buf.len() {
                        let mut local_buf = [0; 9];
                        assert_eq!(
                            put_varint(local_buf.as_mut_slice(), serial_type.0 as u64),
                            n
                        );
                        let buf_len = buf.len();
                        buf[offset_in_buf..].copy_from_slice(&local_buf[..buf_len - offset_in_buf]);
                        return Ok(buf.len());
                    }
                    assert_eq!(
                        put_varint(&mut buf[offset_in_buf..], serial_type.0 as u64),
                        n
                    );
                } else if i_header + n > offset {
                    let mut local_buf = [0; 9];
                    assert_eq!(
                        put_varint(local_buf.as_mut_slice(), serial_type.0 as u64),
                        n
                    );
                    buf[..n - (offset - i_header)]
                        .copy_from_slice(&local_buf[offset - i_header..n]);
                }
                i_header += n;
            }
            assert_eq!(i_header, self.header_size);
        }

        let mut i_data = self.header_size;
        if offset == 0 && buf.len() >= self.payload_size.get() as usize {
            // Optimized path: most case is buf.len() <= self.payload_size. Copy the content
            // with less conditional branches than below.
            for (serial_type, value) in self.values.iter() {
                match serial_type.0 {
                    0 | 8 | 9 => {}
                    st if st <= 6 => {
                        // TODO: Confirm the unreachable has no overhead.
                        let Some(Value::Integer(i)) = value else {
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
                        let Some(Value::Real(d)) = value else {
                            unreachable!("serial type 7 must be Value::Real");
                        };
                        buf[i_data..i_data + 8].copy_from_slice(&d.to_be_bytes());
                        i_data += 8;
                    }
                    _ => {
                        let data = match value {
                            Some(Value::Text(buf)) | Some(Value::Blob(buf)) => buf,
                            _ => unreachable!("serial type must be Value::Text or Value::Blob"),
                        };
                        buf[i_data..i_data + data.len()].copy_from_slice(data);
                        i_data += data.len();
                    }
                }
            }
            assert_eq!(i_data, self.payload_size.get() as usize);
            Ok(i_data)
        } else {
            for (serial_type, value) in self.values.iter() {
                match serial_type.0 {
                    0 | 8 | 9 => {}
                    st if st <= 6 => {
                        let n = if st <= 4 {
                            st as usize
                        } else if st == 5 {
                            6
                        } else {
                            8
                        };
                        if i_data >= offset {
                            let offset_in_buf = i_data - offset;
                            // TODO: Confirm the unreachable has no overhead.
                            let Some(Value::Integer(i)) = value else {
                                unreachable!("serial type 1 ~ 6 must be Value::Integer");
                            };
                            if n + offset_in_buf >= buf.len() {
                                let buf_len = buf.len();
                                buf[offset_in_buf..].copy_from_slice(
                                    &i.to_be_bytes()[8 - n..8 - n + buf_len - offset_in_buf],
                                );
                                return Ok(buf.len());
                            }
                            buf[offset_in_buf..offset_in_buf + n]
                                .copy_from_slice(&i.to_be_bytes()[8 - n..]);
                        } else if i_data + n > offset {
                            let Some(Value::Integer(i)) = value else {
                                unreachable!("serial type 1 ~ 6 must be Value::Integer");
                            };
                            let size_to_copy = n - (offset - i_data);
                            buf[..size_to_copy]
                                .copy_from_slice(&i.to_be_bytes()[8 - size_to_copy..]);
                        }
                        i_data += n;
                    }
                    7 => {
                        const REAL_SIZE: usize = 8;
                        if i_data >= offset {
                            let offset_in_buf = i_data - offset;
                            let Some(Value::Real(d)) = value else {
                                unreachable!("serial type 7 must be Value::Real");
                            };
                            if REAL_SIZE + offset_in_buf >= buf.len() {
                                let buf_len = buf.len();
                                buf[offset_in_buf..]
                                    .copy_from_slice(&d.to_be_bytes()[..buf_len - offset_in_buf]);
                                return Ok(buf.len());
                            }
                            buf[offset_in_buf..offset_in_buf + REAL_SIZE]
                                .copy_from_slice(&d.to_be_bytes());
                        } else if i_data + REAL_SIZE > offset {
                            let Some(Value::Real(d)) = value else {
                                unreachable!("serial type 7 must be Value::Real");
                            };
                            buf[..REAL_SIZE - (offset - i_data)]
                                .copy_from_slice(&d.to_be_bytes()[offset - i_data..]);
                        }
                        i_data += REAL_SIZE;
                    }
                    st => {
                        let n = (st as usize - 12) >> 1;
                        if i_data >= offset {
                            let offset_in_buf = i_data - offset;
                            let data = match value {
                                Some(Value::Text(buf)) | Some(Value::Blob(buf)) => buf,
                                _ => unreachable!("serial type must be Value::Text or Value::Blob"),
                            };
                            if n + offset_in_buf >= buf.len() {
                                let buf_len = buf.len();
                                buf[offset_in_buf..]
                                    .copy_from_slice(&data[..buf_len - offset_in_buf]);
                                return Ok(buf.len());
                            }
                            buf[offset_in_buf..offset_in_buf + n].copy_from_slice(data);
                        } else if i_data + n > offset {
                            let data = match value {
                                Some(Value::Text(buf)) | Some(Value::Blob(buf)) => buf,
                                _ => unreachable!("serial type must be Value::Text or Value::Blob"),
                            };
                            let size_to_copy = std::cmp::min(n - (offset - i_data), buf.len());
                            buf[..size_to_copy].copy_from_slice(
                                &data[offset - i_data..size_to_copy + (offset - i_data)],
                            );
                            if size_to_copy == buf.len() {
                                return Ok(buf.len());
                            }
                        }
                        i_data += n;
                    }
                }
            }
            assert_eq!(i_data, self.payload_size.get() as usize);
            Ok(i_data - offset)
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::cursor::BtreeCursor;
    use crate::payload::SlicePayload;
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
        assert_eq!(record.get(0).unwrap(), None);
        assert_eq!(record.get(1).unwrap(), Some(Value::Integer(1)));
        assert_eq!(record.get(2).unwrap(), None);
        assert_eq!(record.get(3).unwrap(), Some(Value::Integer(0)));
        drop(payload);

        cursor.move_next().unwrap();
        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let mut record = parse_record(&payload).unwrap();
        assert_eq!(record.get(0).unwrap(), Some(Value::Integer(i8::MAX as i64)));
        assert_eq!(record.get(1).unwrap(), Some(Value::Integer(i8::MIN as i64)));
        assert_eq!(
            record.get(2).unwrap(),
            Some(Value::Integer(i16::MAX as i64))
        );
        assert_eq!(
            record.get(3).unwrap(),
            Some(Value::Integer(i16::MIN as i64))
        );
        drop(payload);

        cursor.move_next().unwrap();
        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let mut record = parse_record(&payload).unwrap();
        assert_eq!(
            record.get(0).unwrap(),
            Some(Value::Integer((ONE << 23) - 1))
        );
        assert_eq!(record.get(1).unwrap(), Some(Value::Integer(-(ONE << 23))));
        assert_eq!(
            record.get(2).unwrap(),
            Some(Value::Integer(i32::MAX as i64))
        );
        assert_eq!(
            record.get(3).unwrap(),
            Some(Value::Integer(i32::MIN as i64))
        );
        drop(payload);

        cursor.move_next().unwrap();
        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let mut record = parse_record(&payload).unwrap();
        assert_eq!(
            record.get(0).unwrap(),
            Some(Value::Integer((ONE << 47) - 1))
        );
        assert_eq!(record.get(1).unwrap(), Some(Value::Integer(-(ONE << 47))));
        assert_eq!(record.get(2).unwrap(), Some(Value::Integer(i64::MAX)));
        assert_eq!(record.get(3).unwrap(), Some(Value::Integer(i64::MIN)));
        drop(payload);

        cursor.move_next().unwrap();
        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let mut record = parse_record(&payload).unwrap();
        assert_eq!(record.get(0).unwrap(), Some(Value::Integer(0)));
        assert_eq!(record.get(1).unwrap(), Some(Value::Integer(1)));
        assert_eq!(
            record.get(2).unwrap(),
            Some(Value::Text(b"hello".as_slice().into()))
        );
        assert_eq!(
            record.get(3).unwrap(),
            Some(Value::Blob(
                [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef]
                    .as_slice()
                    .into()
            ))
        );
        drop(payload);

        cursor.move_next().unwrap();
        let (_, payload) = cursor.get_table_payload().unwrap().unwrap();
        let mut record = parse_record(&payload).unwrap();
        assert_eq!(record.get(0).unwrap(), Some(Value::Real(0.5)));
    }

    #[test]
    fn test_parse_real() {
        assert_eq!(
            SerialType(7).parse(0_f64.to_be_bytes().as_slice()).unwrap(),
            Some(Value::Real(0.0))
        );
        assert_eq!(
            SerialType(7)
                .parse(1.1_f64.to_be_bytes().as_slice())
                .unwrap(),
            Some(Value::Real(1.1))
        );
        // NaN
        assert_eq!(
            SerialType(7)
                .parse(f64::NAN.to_be_bytes().as_slice())
                .unwrap(),
            None
        );
    }

    #[test]
    fn test_record_payload() {
        let values = vec![
            None,
            Some(Value::Integer(0)),
            Some(Value::Integer(-1)),
            Some(Value::Integer(1)),
            Some(Value::Integer(2)),
            Some(Value::Integer(i8::MIN as i64)),
            Some(Value::Integer(i8::MAX as i64)),
            Some(Value::Integer(i16::MIN as i64)),
            Some(Value::Integer(i16::MAX as i64)),
            Some(Value::Integer((ONE << 23) - 1)),
            Some(Value::Integer(-(ONE << 23))),
            Some(Value::Integer(i32::MIN as i64)),
            Some(Value::Integer(i32::MAX as i64)),
            Some(Value::Integer((ONE << 47) - 1)),
            Some(Value::Integer(-(ONE << 47))),
            Some(Value::Integer(i64::MIN)),
            Some(Value::Integer(i64::MAX)),
            Some(Value::Real(0.0)),
            Some(Value::Real(12345.6)),
            Some(Value::Text(Buffer::Owned(b"hello".to_vec()))),
            Some(Value::Blob(Buffer::Owned(b"world".to_vec()))),
        ];
        let record = values.iter().map(|v| v.as_ref()).collect::<Vec<_>>();
        let payload = RecordPayload::new(&record).unwrap();
        let mut buf = vec![0; payload.size().get() as usize];
        assert_eq!(payload.load(0, &mut buf).unwrap(), buf.len());
        let payload2 = SlicePayload::new(&buf).unwrap();
        let mut record = Record::parse(&payload2).unwrap();
        for (i, value) in values.iter().enumerate() {
            assert_eq!(record.get(i).unwrap(), *value, "index {}", i);
        }

        for i in 9..buf.len() {
            buf.fill(0);
            assert_eq!(payload.load(0, &mut buf[..i]).unwrap(), i, "split: {}", i);
            assert_eq!(
                payload.load(i, &mut buf[i..]).unwrap(),
                buf.len() - i,
                "split: {}",
                i
            );
            let payload2 = SlicePayload::new(&buf).unwrap();
            let mut record = Record::parse(&payload2).unwrap();
            for (j, value) in values.iter().enumerate() {
                assert_eq!(record.get(j).unwrap(), *value, "split: {}, value: {}", i, j);
            }
        }

        // No data but header only.
        let mut buf = vec![0; 2];
        assert_eq!(
            RecordPayload::new(&[None])
                .unwrap()
                .load(0, &mut buf)
                .unwrap(),
            2
        );
        assert_eq!(buf, vec![2, 0]);

        let mut buf = vec![0; 127];
        assert_eq!(
            RecordPayload::new(&[None; 126])
                .unwrap()
                .load(0, &mut buf)
                .unwrap(),
            127
        );
        assert_eq!(buf[0], 127);
        assert_eq!(&buf[1..], &[0; 126]);
        assert_eq!(
            Record::parse(&SlicePayload::new(&buf).unwrap())
                .unwrap()
                .len(),
            126
        );

        let mut buf = vec![0; 129];
        assert_eq!(
            RecordPayload::new(&[None; 127])
                .unwrap()
                .load(0, &mut buf)
                .unwrap(),
            129
        );
        assert_eq!(&buf[..2], &[129, 1]);
        assert_eq!(&buf[2..], &[0; 127]);
        assert_eq!(
            Record::parse(&SlicePayload::new(&buf).unwrap())
                .unwrap()
                .len(),
            127
        );

        let mut buf = vec![0; 130];
        assert_eq!(
            RecordPayload::new(&[None; 128])
                .unwrap()
                .load(0, &mut buf)
                .unwrap(),
            130
        );
        assert_eq!(&buf[..2], &[129, 2]);
        assert_eq!(&buf[2..], &[0; 128]);
        assert_eq!(
            Record::parse(&SlicePayload::new(&buf).unwrap())
                .unwrap()
                .len(),
            128
        );

        // Multi byte header (text).
        let mut buf = vec![0; 61];
        assert_eq!(
            RecordPayload::new(&[Some(&Value::Text(Buffer::Owned(vec![0x11; 58])))])
                .unwrap()
                .load(0, &mut buf)
                .unwrap(),
            61
        );
        assert_eq!(buf[..3], vec![3, 129, 1]);
        assert_eq!(buf.len() - 3, 58);
        assert_eq!(
            Record::parse(&SlicePayload::new(&buf).unwrap())
                .unwrap()
                .get(0)
                .unwrap(),
            Some(Value::Text(Buffer::Owned(vec![0x11; 58])))
        );

        // Multi byte header (blob).
        let mut buf = vec![0; 61];
        assert_eq!(
            RecordPayload::new(&[Some(&Value::Blob(Buffer::Owned(vec![0x11; 58])))])
                .unwrap()
                .load(0, &mut buf)
                .unwrap(),
            61
        );
        assert_eq!(buf[..3], vec![3, 129, 0]);
        assert_eq!(buf.len() - 3, 58);
        assert_eq!(
            Record::parse(&SlicePayload::new(&buf).unwrap())
                .unwrap()
                .get(0)
                .unwrap(),
            Some(Value::Blob(Buffer::Owned(vec![0x11; 58])))
        );
    }
}
