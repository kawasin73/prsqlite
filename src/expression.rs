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

use crate::parser::BinaryOp;
use crate::parser::CompareOp;
use crate::parser::Expr;
use crate::parser::UnaryOp;
use crate::schema::calc_collation;
use crate::schema::calc_type_affinity;
use crate::schema::ColumnNumber;
use crate::schema::Table;
use crate::value::Buffer;
use crate::value::Collation;
use crate::value::ConstantValue;
use crate::value::TypeAffinity;
use crate::value::Value;
use crate::value::ValueCmp;
use crate::value::DEFAULT_COLLATION;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum CollateOrigin {
    Column,
    Expression,
}

fn filter_expression_collation(
    collation: Option<(&Collation, CollateOrigin)>,
) -> Option<(&Collation, CollateOrigin)> {
    match collation {
        Some((_, CollateOrigin::Expression)) => collation,
        _ => None,
    }
}

pub trait DataContext {
    fn get_column_value(&self, column_idx: &ColumnNumber) -> anyhow::Result<Option<Value>>;
}

#[derive(Debug, Clone)]
pub enum Expression {
    Column((ColumnNumber, TypeAffinity, Collation)),
    UnaryOperator {
        operator: UnaryOp,
        expr: Box<Expression>,
    },
    Collate {
        expr: Box<Expression>,
        collation: Collation,
    },
    BinaryOperator {
        operator: BinaryOp,
        left: Box<Expression>,
        right: Box<Expression>,
    },
    Cast {
        expr: Box<Expression>,
        type_affinity: TypeAffinity,
    },
    Null,
    Const(ConstantValue),
}

type ExecutionResult<'a> = (
    Option<Value<'a>>,
    Option<TypeAffinity>,
    Option<(&'a Collation, CollateOrigin)>,
);

impl Expression {
    pub fn from(expr: Expr, table: Option<&Table>) -> anyhow::Result<Self> {
        match expr {
            Expr::Null => Ok(Self::Null),
            Expr::Integer(i) => Ok(Self::Const(ConstantValue::Integer(i))),
            Expr::Real(f) => Ok(Self::Const(ConstantValue::Real(f))),
            Expr::Text(text) => Ok(Self::Const(ConstantValue::Text(text.dequote()))),
            Expr::Blob(hex) => Ok(Self::Const(ConstantValue::Blob(hex.decode()))),
            Expr::UnaryOperator { operator, expr } => Ok(Self::UnaryOperator {
                operator,
                expr: Box::new(Self::from(*expr, table)?),
            }),
            Expr::Collate {
                expr,
                collation_name,
            } => Ok(Self::Collate {
                expr: Box::new(Self::from(*expr, table)?),
                collation: calc_collation(&collation_name)?,
            }),
            Expr::BinaryOperator {
                operator,
                left,
                right,
            } => Ok(Self::BinaryOperator {
                operator,
                left: Box::new(Self::from(*left, table)?),
                right: Box::new(Self::from(*right, table)?),
            }),
            Expr::Column(column_name) => {
                if let Some(table) = table {
                    let column_name = column_name.dequote();
                    table
                        .get_column(&column_name)
                        .map(Self::Column)
                        .ok_or(anyhow::anyhow!(
                            "column not found: {}",
                            std::str::from_utf8(&column_name).unwrap_or_default()
                        ))
                } else {
                    bail!("no table context is not specified");
                }
            }
            Expr::Cast { expr, type_name } => Ok(Self::Cast {
                expr: Box::new(Self::from(*expr, table)?),
                type_affinity: calc_type_affinity(&type_name),
            }),
        }
    }

    /// Execute the expression and return the result.
    ///
    /// TODO: The row should be a context object.
    pub fn execute<'a, D: DataContext>(
        &'a self,
        row: Option<&'a D>,
    ) -> anyhow::Result<ExecutionResult<'a>> {
        match self {
            Self::Column((idx, affinity, collation)) => {
                if let Some(row) = row {
                    Ok((
                        row.get_column_value(idx)?,
                        Some(*affinity),
                        Some((collation, CollateOrigin::Column)),
                    ))
                } else {
                    bail!("column value is not available");
                }
            }
            Self::UnaryOperator { operator, expr } => {
                let (value, _, collation) = expr.execute(row)?;
                let value = match operator {
                    UnaryOp::BitNot => value.map(|v| Value::Integer(!v.as_integer())),
                    UnaryOp::Minus => value.map(|v| match v {
                        Value::Integer(i) => Value::Integer(-i),
                        Value::Real(d) => Value::Real(-d),
                        Value::Text(_) | Value::Blob(_) => Value::Integer(0),
                    }),
                };
                Ok((value, None, filter_expression_collation(collation)))
            }
            Self::Collate { expr, collation } => {
                let (value, affinity, _) = expr.execute(row)?;
                Ok((
                    value,
                    // Type affinity is preserved.
                    affinity,
                    Some((collation, CollateOrigin::Expression)),
                ))
            }
            Self::BinaryOperator {
                operator,
                left,
                right,
            } => {
                let (left_value, left_affinity, left_collation) = left.execute(row)?;
                let (right_value, right_affinity, right_collation) = right.execute(row)?;

                // TODO: Confirm whether collation is preserved after NULL.
                let (mut left_value, mut right_value) = match (left_value, right_value) {
                    (None, _) | (_, None) => return Ok((None, None, None)),
                    (Some(left_value), Some(right_value)) => (left_value, right_value),
                };

                let collation = match (left_collation, right_collation) {
                    (None, _) => right_collation,
                    (Some((_, CollateOrigin::Column)), Some((_, CollateOrigin::Expression))) => {
                        right_collation
                    }
                    _ => left_collation,
                };
                let next_collation = filter_expression_collation(collation);

                match operator {
                    BinaryOp::Compare(compare_op) => {
                        // Type Conversions Prior To Comparison
                        match (left_affinity, right_affinity) {
                            (
                                Some(TypeAffinity::Integer)
                                | Some(TypeAffinity::Real)
                                | Some(TypeAffinity::Numeric),
                                Some(TypeAffinity::Text) | Some(TypeAffinity::Blob) | None,
                            ) => {
                                right_value = right_value.apply_numeric_affinity();
                            }
                            (
                                Some(TypeAffinity::Text) | Some(TypeAffinity::Blob) | None,
                                Some(TypeAffinity::Integer)
                                | Some(TypeAffinity::Real)
                                | Some(TypeAffinity::Numeric),
                            ) => {
                                left_value = left_value.apply_numeric_affinity();
                            }
                            (Some(TypeAffinity::Text), None) => {
                                right_value = right_value.apply_text_affinity();
                            }
                            (None, Some(TypeAffinity::Text)) => {
                                left_value = left_value.apply_text_affinity();
                            }
                            _ => {}
                        }

                        let cmp = ValueCmp::new(
                            &left_value,
                            collation.map(|(c, _)| c).unwrap_or(&DEFAULT_COLLATION),
                        )
                        .compare(&right_value);

                        let result = match compare_op {
                            CompareOp::Eq => cmp == Ordering::Equal,
                            CompareOp::Ne => cmp != Ordering::Equal,
                            CompareOp::Lt => cmp == Ordering::Less,
                            CompareOp::Le => cmp != Ordering::Greater,
                            CompareOp::Gt => cmp == Ordering::Greater,
                            CompareOp::Ge => cmp != Ordering::Less,
                        };
                        if result {
                            Ok((Some(Value::Integer(1)), None, next_collation))
                        } else {
                            Ok((Some(Value::Integer(0)), None, next_collation))
                        }
                    }
                    BinaryOp::Concat => {
                        // Both operands are forcibly converted to text before concatination. Both
                        // are not null.
                        let left = left_value.force_text_buffer();
                        let right = right_value.force_text_buffer();
                        let mut buffer = match left {
                            Buffer::Owned(buf) => buf,
                            Buffer::Ref(buf) => {
                                let mut buffer = Vec::with_capacity(buf.len() + right.len());
                                buffer.extend(buf);
                                buffer
                            }
                        };
                        buffer.extend(right.iter());
                        Ok((
                            Some(Value::Text(Buffer::Owned(buffer))),
                            None,
                            next_collation,
                        ))
                    }
                }
            }
            Self::Cast {
                expr,
                type_affinity,
            } => {
                let (value, _affinity, collation) = expr.execute(row)?;
                Ok((
                    value.map(|v| v.force_apply_type_affinity(*type_affinity)),
                    Some(*type_affinity),
                    collation,
                ))
            }
            Self::Null => Ok((None, None, None)),
            Self::Const(value) => Ok((Some(value.as_value()), None, None)),
        }
    }
}
