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
use std::fmt::Display;

use crate::btree::BtreeContext;
use crate::cursor::BtreeCursor;
use crate::cursor::BtreePayload;
use crate::expression::DataContext;
use crate::expression::Expression;
use crate::pager::PageId;
use crate::pager::Pager;
use crate::parser::BinaryOp;
use crate::parser::CompareOp;
use crate::payload::LocalPayload;
use crate::payload::Payload;
use crate::record::parse_record;
use crate::record::parse_record_header;
use crate::record::SerialType;
use crate::schema::ColumnNumber;
use crate::schema::Table;
use crate::value::Collation;
use crate::value::ConstantValue;
use crate::value::TypeAffinity;
use crate::value::Value;
use crate::value::ValueCmp;

#[derive(Debug)]
pub enum Error {
    Cursor(crate::cursor::Error),
    Record(anyhow::Error),
    Expression(crate::expression::Error),
}

impl From<crate::cursor::Error> for Error {
    fn from(e: crate::cursor::Error) -> Self {
        Self::Cursor(e)
    }
}

impl From<crate::expression::Error> for Error {
    fn from(e: crate::expression::Error) -> Self {
        Self::Expression(e)
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Cursor(e) => Some(e),
            Self::Record(e) => e.source(),
            Self::Expression(e) => Some(e),
        }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Cursor(e) => f.write_fmt(format_args!("cursor: {}", e)),
            Self::Record(e) => f.write_fmt(format_args!("record: {}", e)),
            Self::Expression(e) => f.write_fmt(format_args!("expression: {}", e)),
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub enum QueryPlan {
    FullScan,
    IndexScan(IndexInfo),
    RowId(i64),
}

impl QueryPlan {
    pub fn generate(table: &Table, filter: &Expression) -> Self {
        let mut plan = Self::FullScan;

        if let Expression::BinaryOperator {
            operator: BinaryOp::Compare(CompareOp::Eq),
            left,
            right,
        } = filter
        {
            match (left.as_ref(), right.as_ref()) {
                (
                    Expression::Column((ColumnNumber::RowId, _, _)),
                    Expression::Const(ConstantValue::Integer(value)),
                )
                | (
                    Expression::Const(ConstantValue::Integer(value)),
                    Expression::Column((ColumnNumber::RowId, _, _)),
                ) => plan = Self::RowId(*value),
                (
                    Expression::Column((column_number, type_affinity, collation)),
                    Expression::Const(const_value),
                )
                | (
                    Expression::Const(const_value),
                    Expression::Column((column_number, type_affinity, collation)),
                ) => {
                    let mut next_index = table.indexes.as_ref();
                    while let Some(index) = next_index {
                        if index.columns[0] == *column_number {
                            break;
                        }
                        next_index = index.next.as_ref();
                    }
                    if let Some(index) = next_index {
                        let value = match type_affinity {
                            TypeAffinity::Integer | TypeAffinity::Real | TypeAffinity::Numeric => {
                                ConstantValue::copy_from(
                                    const_value.as_value().apply_numeric_affinity(),
                                )
                            }
                            TypeAffinity::Text => ConstantValue::copy_from(
                                const_value.as_value().apply_text_affinity(),
                            ),
                            TypeAffinity::Blob => ConstantValue::copy_from(const_value.as_value()),
                        };

                        // TODO: Consider collation of constant value.
                        plan = Self::IndexScan(IndexInfo {
                            page_id: index.root_page_id,
                            keys: vec![(value, collation.clone())],
                            n_extra: index.columns.len() - 1,
                        });
                    }
                }
                _ => {}
            };
        };
        plan
    }

    pub fn index_page_id(&self) -> Option<PageId> {
        match self {
            Self::FullScan | Self::RowId(_) => None,
            Self::IndexScan(index_info) => Some(index_info.page_id),
        }
    }
}

pub struct IndexInfo {
    page_id: PageId,
    keys: Vec<(ConstantValue, Collation)>,
    n_extra: usize,
}

enum PlanExecutor<'a> {
    Full,
    Index(IndexCursor<'a>),
    RowId(Option<i64>),
}

pub struct Query<'a> {
    cursor: BtreeCursor<'a>,
    plan: PlanExecutor<'a>,
    filter: &'a Expression,
    deleted: bool,
}

impl<'a> Query<'a> {
    pub fn new(
        table_page_id: PageId,
        pager: &'a Pager,
        bctx: &'a BtreeContext,
        plan: &'a QueryPlan,
        filter: &'a Expression,
    ) -> Result<Self> {
        let plan = match plan {
            QueryPlan::FullScan => PlanExecutor::Full,
            QueryPlan::IndexScan(index_info) => PlanExecutor::Index(IndexCursor::new(
                index_info.page_id,
                pager,
                bctx,
                index_info,
            )?),
            QueryPlan::RowId(rowid) => PlanExecutor::RowId(Some(*rowid)),
        };

        Ok(Self {
            cursor: BtreeCursor::new(table_page_id, pager, bctx)?,
            plan,
            filter,
            deleted: false,
        })
    }

    pub fn next(&mut self) -> Result<Option<RowData<'_>>> {
        let mut headers;
        let mut content_offset;
        let mut tmp_buf = Vec::new();
        let mut use_local_buffer;

        loop {
            match &mut self.plan {
                PlanExecutor::Full => {
                    if !self.cursor.is_initialized() {
                        self.cursor.move_to_first()?;
                    } else if !self.deleted {
                        self.cursor.move_next()?;
                    } else {
                        self.deleted = false;
                    }
                }
                PlanExecutor::Index(index_cursor) => {
                    let rowid = index_cursor.next(self.deleted)?;
                    self.deleted = false;
                    if let Some(rowid) = rowid {
                        self.cursor.table_move_to(rowid)?;
                    } else {
                        return Ok(None);
                    }
                }
                PlanExecutor::RowId(rowid) => {
                    if let Some(rowid) = rowid.take() {
                        self.cursor.table_move_to(rowid)?;
                    } else {
                        return Ok(None);
                    }
                }
            }

            let Some((rowid, payload)) = self.cursor.get_table_payload()? else {
                return Ok(None);
            };

            headers = parse_record_header(&payload).map_err(Error::Record)?;
            assert!(!headers.is_empty());

            content_offset = headers[0].1;
            let last_header = &headers[headers.len() - 1];
            let content_size =
                last_header.1 + last_header.0.content_size() as usize - content_offset;
            assert!(content_offset + content_size <= payload.size().get() as usize);
            use_local_buffer = payload.buf().len() >= (content_offset + content_size);
            if !use_local_buffer {
                tmp_buf.resize(content_size, 0);
                let n = payload.load(content_offset, &mut tmp_buf)?;
                assert_eq!(n, content_size);
            };

            let data = RowData {
                rowid,
                payload,
                tmp_buf,
                headers,
                use_local_buffer,
                content_offset,
            };
            let skip = matches!(
                self.filter.execute(Some(&data))?.0,
                None | Some(Value::Integer(0))
            );
            RowData {
                rowid: _,
                payload: _,
                tmp_buf,
                headers,
                use_local_buffer,
                content_offset,
            } = data;
            if !skip {
                break;
            }
        }

        let Some((rowid, payload)) = self.cursor.get_table_payload()? else {
            unreachable!("cursor must point to a valid row");
        };

        Ok(Some(RowData {
            headers,
            rowid,
            payload,
            content_offset,
            use_local_buffer,
            tmp_buf,
        }))
    }

    pub fn delete(&mut self) -> Result<()> {
        self.cursor.delete()?;
        if let PlanExecutor::Index(index_cursor) = &mut self.plan {
            index_cursor.cursor.delete()?;
        }
        self.deleted = true;
        Ok(())
    }
}

struct IndexCursor<'a> {
    cursor: BtreeCursor<'a>,
    index: &'a IndexInfo,
}

impl<'a> IndexCursor<'a> {
    fn new(
        index_page_id: PageId,
        pager: &'a Pager,
        bctx: &'a BtreeContext,
        index: &'a IndexInfo,
    ) -> Result<Self> {
        Ok(Self {
            cursor: BtreeCursor::new(index_page_id, pager, bctx)?,
            index,
        })
    }

    fn next(&mut self, deleted: bool) -> Result<Option<i64>> {
        if !self.cursor.is_initialized() {
            // TODO: IndexInfo should hold ValueCmp instead of ConstantValue.
            let tmp_keys = self
                .index
                .keys
                .iter()
                .map(|(v, c)| (v.as_value(), c))
                .collect::<Vec<_>>();
            let mut comparators =
                Vec::with_capacity(self.index.keys.len() + self.index.n_extra + 1);
            comparators.extend(tmp_keys.iter().map(|(v, c)| Some(ValueCmp::new(v, c))));
            // +1 for rowid
            comparators.extend((0..self.index.n_extra + 1).map(|_| None));
            self.cursor.index_move_to(&comparators)?;
        } else if !deleted {
            self.cursor.move_next()?;
        }

        let Some(index_payload) = self.cursor.get_index_payload()? else {
            return Ok(None);
        };
        let mut record = parse_record(&index_payload).map_err(Error::Record)?;
        let keys = self.index.keys.as_slice();
        if record.len() < keys.len() {
            return Err(Error::Record(anyhow::anyhow!("index payload is too short")));
        }
        for (i, (key, collation)) in keys.iter().enumerate() {
            if let Some(value) = record.get(i).map_err(Error::Record)? {
                if ValueCmp::new(&key.as_value(), collation).compare(&value) == Ordering::Equal {
                    continue;
                }
            }
            return Ok(None);
        }
        let Some(Value::Integer(rowid)) = record.get(record.len() - 1).map_err(Error::Record)?
        else {
            return Err(Error::Record(anyhow::anyhow!(
                "rowid in index is not integer"
            )));
        };

        Ok(Some(rowid))
    }
}

pub struct RowData<'a> {
    rowid: i64,
    payload: BtreePayload<'a>,
    headers: Vec<(SerialType, usize)>,
    content_offset: usize,
    use_local_buffer: bool,
    tmp_buf: Vec<u8>,
}

impl<'a> DataContext for RowData<'a> {
    fn get_column_value(
        &self,
        column_idx: &ColumnNumber,
    ) -> std::result::Result<Option<Value>, Box<dyn std::error::Error + Sync + Send>> {
        match column_idx {
            ColumnNumber::Column(idx) => {
                if let Some((serial_type, offset)) = self.headers.get(*idx) {
                    let contents_buffer = if self.use_local_buffer {
                        &self.payload.buf()[self.content_offset..]
                    } else {
                        &self.tmp_buf
                    };
                    let offset = offset - self.content_offset;
                    if contents_buffer.len() < offset
                        || contents_buffer.len() - offset < serial_type.content_size() as usize
                    {
                        return Err(anyhow::anyhow!("payload does not have enough size").into());
                    }
                    Ok(serial_type.parse(&contents_buffer[offset..]))
                } else {
                    Ok(None)
                }
            }
            ColumnNumber::RowId => Ok(Some(Value::Integer(self.rowid))),
        }
    }
}
