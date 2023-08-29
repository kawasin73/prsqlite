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
use std::io::Write;

use crate::utils::parse_float;
use crate::utils::parse_integer;
use crate::utils::ParseIntegerResult;

// TODO: Own the buffer of Text and Blob.
#[derive(Debug, Clone)]
pub enum Value<'a> {
    Null,
    Integer(i64),
    Real(f64),
    // NOTE: Any text is not guaranteed to be valid UTF-8.
    Text(&'a [u8]),
    Blob(&'a [u8]),
}

impl<'a> Value<'a> {
    pub fn display<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        match self {
            Value::Null => Ok(()),
            Value::Integer(i) => write!(w, "{i}"),
            Value::Real(d) => write!(w, "{d}"),
            Value::Blob(b) => w.write_all(b),
            Value::Text(t) => w.write_all(t),
        }
    }

    /// Convert the text value to a numeric value if it is well-formed.
    /// Otherwise, return the original value.
    pub fn apply_numeric_affinity(self) -> Value<'a> {
        match self {
            Value::Null => Value::Null,
            Value::Integer(i) => Value::Integer(i),
            Value::Real(d) => Value::Real(d),
            Value::Text(t) => match parse_integer(t) {
                (true, ParseIntegerResult::Integer(i)) => Value::Integer(i),
                _ => {
                    let (valid, _, d) = parse_float(t);
                    if valid {
                        let di = real_to_int(d);
                        if is_real_same_as_int(d, di) {
                            Value::Integer(di)
                        } else {
                            Value::Real(d)
                        }
                    } else {
                        Value::Text(t)
                    }
                }
            },
            Value::Blob(b) => Value::Blob(b),
        }
    }

    /// Convert the value to a text value.
    ///
    /// For [Value::Text] and [Value::Blob] values, this just changes the type
    /// of the value.
    ///
    /// For [Value::Integer] and [Value::Real] values, this
    /// converts the value to a text value.
    ///
    /// This does not support [Value::Null] values.
    pub fn apply_text_affinity<'b>(self, text_buf: &'b mut Vec<u8>) -> Value<'b>
    where
        'a: 'b,
    {
        assert_ne!(self, Value::Null);
        match self {
            Value::Null => unreachable!(),
            Value::Integer(i) => {
                write!(text_buf, "{}", i).unwrap();
                Value::Text(text_buf)
            }
            Value::Real(d) => {
                // TODO: Use the same format as SQLite "%!.15g".
                write!(text_buf, "{}", d).unwrap();
                Value::Text(text_buf)
            }
            Value::Text(t) => Value::Text(t),
            Value::Blob(b) => Value::Text(b),
        }
    }

    /// Convert the [Value] to the type of [TypeAffinity] even if the conversion
    /// is lossy.
    ///
    /// This is used for the CAST expression.
    ///
    /// https://www.sqlite.org/lang_expr.html#castexpr
    pub fn force_apply_type_affinity(self, type_affinity: TypeAffinity) -> Value<'a> {
        match type_affinity {
            TypeAffinity::Numeric => match self {
                Value::Null => Value::Null,
                Value::Integer(i) => Value::Integer(i),
                Value::Real(d) => Value::Real(d),
                Value::Text(buf) | Value::Blob(buf) => {
                    let (_, pure_integer, d) = parse_float(buf);
                    let mut v = if pure_integer {
                        let (_, parsed_int) = parse_integer(buf);
                        match parsed_int {
                            ParseIntegerResult::Integer(i) => Value::Integer(i),
                            _ => Value::Real(d),
                        }
                    } else {
                        Value::Real(d)
                    };
                    if let Value::Real(d) = &v {
                        let di = real_to_int(*d);
                        if is_real_same_as_int(*d, di) {
                            v = Value::Integer(di);
                        }
                    }
                    v
                }
            },
            TypeAffinity::Integer => match self {
                Value::Null => Value::Null,
                Value::Integer(i) => Value::Integer(i),
                Value::Real(d) => Value::Integer(real_to_int(d)),
                Value::Text(buf) | Value::Blob(buf) => {
                    let (_, parsed_int) = parse_integer(buf);
                    match parsed_int {
                        ParseIntegerResult::Integer(i) => Value::Integer(i),
                        ParseIntegerResult::Empty => Value::Integer(0),
                        ParseIntegerResult::MaxPlusOne | ParseIntegerResult::TooBig(true) => {
                            Value::Integer(i64::MAX)
                        }
                        ParseIntegerResult::TooBig(false) => Value::Integer(i64::MIN),
                    }
                }
            },
            TypeAffinity::Real => match self {
                Value::Null => Value::Null,
                Value::Integer(i) => Value::Real(i as f64),
                Value::Real(d) => Value::Real(d),
                Value::Text(buf) | Value::Blob(buf) => {
                    let (_, _, d) = parse_float(buf);
                    Value::Real(d)
                }
            },
            TypeAffinity::Text | TypeAffinity::Blob => {
                let value_type = if type_affinity == TypeAffinity::Text {
                    Value::Text
                } else {
                    Value::Blob
                };
                match self {
                    Value::Null => Value::Null,
                    Value::Text(t) => value_type(t),
                    Value::Blob(b) => value_type(b),
                    _ => todo!("apply_type_affinity text"),
                }
            }
        }
    }
}

/// sqlite3RealSameAsInt() in vdbemem.c of SQLite
fn is_real_same_as_int(d: f64, i: i64) -> bool {
    let di = i as f64;
    d == 0.0
        || (d.to_ne_bytes() == di.to_ne_bytes()
            && (-2251799813685248..2251799813685248).contains(&i))
}

/// doubleToInt64() in vdbemem.c of SQLite.
fn real_to_int(d: f64) -> i64 {
    if d >= i64::MAX as f64 {
        i64::MAX
    } else if d <= i64::MIN as f64 {
        i64::MIN
    } else {
        d as i64
    }
}

impl PartialEq for Value<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

/// SQLite does not handle NaN and it converts NaN to NULL.
impl Eq for Value<'_> {}

impl PartialOrd for Value<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// https://www.sqlite.org/datatype3.html#comparison_expressions
impl Ord for Value<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Value::Null, Value::Null) => Ordering::Equal,
            (Value::Null, _) => Ordering::Less,
            (_, Value::Null) => Ordering::Greater,
            (Value::Integer(i1), Value::Integer(i2)) => i1.cmp(i2),
            (Value::Integer(i1), Value::Real(d2)) => cmp_int_real(*i1, *d2),
            (Value::Real(d1), Value::Integer(i2)) => cmp_int_real(*i2, *d1).reverse(),
            // The value never be NaN.
            (Value::Real(d1), Value::Real(d2)) => d1.partial_cmp(d2).unwrap(),
            (Value::Integer(_), _) => Ordering::Less,
            (_, Value::Integer(_)) => Ordering::Greater,
            (Value::Real(_), _) => Ordering::Less,
            (_, Value::Real(_)) => Ordering::Greater,
            // TODO: Use collation.
            (Value::Text(t1), Value::Text(t2)) => t1.cmp(t2),
            (Value::Text(_), Value::Blob(_)) => Ordering::Less,
            (Value::Blob(_), Value::Text(_)) => Ordering::Greater,
            (Value::Blob(b1), Value::Blob(b2)) => b1.cmp(b2),
        }
    }
}

/// Compare i64 and f64
///
/// This comes from sqlite3IntFloatCompare().
fn cmp_int_real(i: i64, r: f64) -> Ordering {
    if r < -9223372036854775808.0 {
        return Ordering::Greater;
    } else if r >= 9223372036854775808.0 {
        return Ordering::Less;
    }

    match i.cmp(&(r as i64)) {
        Ordering::Less => return Ordering::Less,
        Ordering::Greater => return Ordering::Greater,
        Ordering::Equal => {}
    }

    let ir = i as f64;
    if ir < r {
        return Ordering::Less;
    } else if ir > r {
        return Ordering::Greater;
    }
    Ordering::Equal
}

/// Data type affinity.
///
/// https://www.sqlite.org/datatype3.html#type_affinity
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TypeAffinity {
    Integer,
    Text,
    Blob,
    Real,
    Numeric,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_compare() {
        assert_eq!(Value::Null.cmp(&Value::Null), Ordering::Equal);
        assert_eq!(Value::Null.cmp(&Value::Integer(0)), Ordering::Less);
        assert_eq!(Value::Null.cmp(&Value::Real(0.0)), Ordering::Less);
        assert_eq!(Value::Null.cmp(&Value::Text(b"")), Ordering::Less);
        assert_eq!(Value::Null.cmp(&Value::Blob(b"")), Ordering::Less);
        assert_eq!(Value::Integer(0).cmp(&Value::Null), Ordering::Greater);
        assert_eq!(
            Value::Integer(12345).cmp(&Value::Integer(12345)),
            Ordering::Equal
        );
        assert_eq!(
            Value::Integer(12345).cmp(&Value::Integer(12346)),
            Ordering::Less
        );
        assert_eq!(
            Value::Integer(12345).cmp(&Value::Real(12345.0)),
            Ordering::Equal
        );
        assert_eq!(
            Value::Integer(12345).cmp(&Value::Real(12345.1)),
            Ordering::Less
        );
        assert_eq!(
            Value::Integer(-9223372036854775808).cmp(&Value::Real(-9223372036854775808.0)),
            Ordering::Equal
        );
        assert_eq!(
            Value::Integer(-9223372036854775808).cmp(&Value::Real(-9223372036854775807.0)),
            Ordering::Equal
        );
        assert_eq!(
            Value::Integer(9223372036854775807).cmp(&Value::Real(9223372036854775807.0)),
            Ordering::Less
        );
        assert_eq!(
            Value::Integer(9223372036854775807).cmp(&Value::Real(9223372036854775806.0)),
            Ordering::Less
        );
        assert_eq!(
            Value::Integer(12345).cmp(&Value::Text(b"12345")),
            Ordering::Less
        );
        assert_eq!(Value::Integer(12345).cmp(&Value::Text(b"")), Ordering::Less);
        assert_eq!(Value::Integer(12345).cmp(&Value::Blob(b"")), Ordering::Less);
        assert_eq!(Value::Real(1234.5).cmp(&Value::Null), Ordering::Greater);
        assert_eq!(
            Value::Real(12345.0).cmp(&Value::Integer(12345)),
            Ordering::Equal
        );
        assert_eq!(
            Value::Real(12345.0).cmp(&Value::Integer(12346)),
            Ordering::Less
        );
        assert_eq!(
            Value::Real(1234.5).cmp(&Value::Real(1234.5)),
            Ordering::Equal
        );
        assert_eq!(
            Value::Real(1234.5).cmp(&Value::Real(1234.6)),
            Ordering::Less
        );
        assert_eq!(Value::Real(1234.5).cmp(&Value::Text(b"")), Ordering::Less);
        assert_eq!(Value::Real(1234.5).cmp(&Value::Blob(b"")), Ordering::Less);
        assert_eq!(Value::Text(b"abcde").cmp(&Value::Null), Ordering::Greater);
        assert_eq!(
            Value::Text(b"").cmp(&Value::Integer(i64::MAX)),
            Ordering::Greater
        );
        assert_eq!(
            Value::Text(b"").cmp(&Value::Real(f64::MAX)),
            Ordering::Greater
        );
        assert_eq!(
            Value::Text(b"abcde").cmp(&Value::Text(b"abcde")),
            Ordering::Equal
        );
        assert_eq!(
            Value::Text(b"abcde").cmp(&Value::Text(b"abcdf")),
            Ordering::Less
        );
        assert_eq!(
            Value::Text(b"abcde").cmp(&Value::Text(b"abcde0")),
            Ordering::Less
        );
        assert_eq!(
            Value::Text(b"abcde").cmp(&Value::Text(b"abcdd")),
            Ordering::Greater
        );
        assert_eq!(
            Value::Text(b"abcde").cmp(&Value::Blob(b"abcde")),
            Ordering::Less
        );
        assert_eq!(Value::Text(b"abcde").cmp(&Value::Blob(b"")), Ordering::Less);
        assert_eq!(Value::Blob(b"").cmp(&Value::Null), Ordering::Greater);
        assert_eq!(
            Value::Blob(b"").cmp(&Value::Integer(i64::MAX)),
            Ordering::Greater
        );
        assert_eq!(
            Value::Blob(b"").cmp(&Value::Real(f64::MAX)),
            Ordering::Greater
        );
        assert_eq!(
            Value::Blob(b"abcde").cmp(&Value::Text(b"abcde")),
            Ordering::Greater
        );
        assert_eq!(
            Value::Blob(b"abcde").cmp(&Value::Blob(b"abcde")),
            Ordering::Equal
        );
        assert_eq!(
            Value::Blob(b"abcde").cmp(&Value::Blob(b"abcdf")),
            Ordering::Less
        );
        assert_eq!(
            Value::Blob(b"abcde").cmp(&Value::Blob(b"abcde0")),
            Ordering::Less
        );
        assert_eq!(
            Value::Blob(b"abcde").cmp(&Value::Blob(b"abcdd")),
            Ordering::Greater
        );
    }

    #[test]
    fn test_apply_numeric_affinity() {
        assert_eq!(Value::Null.apply_numeric_affinity(), Value::Null);

        assert_eq!(
            Value::Integer(12345).apply_numeric_affinity(),
            Value::Integer(12345)
        );

        assert_eq!(
            Value::Real(12345.1).apply_numeric_affinity(),
            Value::Real(12345.1)
        );

        assert_eq!(
            Value::Text(b"12345").apply_numeric_affinity(),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b" 12345 ").apply_numeric_affinity(),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b"9223372036854775807").apply_numeric_affinity(),
            Value::Integer(9223372036854775807)
        );
        assert_eq!(
            Value::Text(b"-9223372036854775808").apply_numeric_affinity(),
            Value::Integer(-9223372036854775808)
        );
        assert_eq!(
            Value::Text(b"0.0").apply_numeric_affinity(),
            Value::Integer(0)
        );
        assert_eq!(
            Value::Text(b"12345.0").apply_numeric_affinity(),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b"12345.6").apply_numeric_affinity(),
            Value::Real(12345.6)
        );
        assert_eq!(
            Value::Text(b" 12345.6 ").apply_numeric_affinity(),
            Value::Real(12345.6)
        );
        assert_eq!(
            Value::Text(b"12345.6e+10").apply_numeric_affinity(),
            Value::Real(12345.6e10)
        );
        assert_eq!(
            Value::Text(b"12345e-1").apply_numeric_affinity(),
            Value::Real(1234.5)
        );
        assert_eq!(
            Value::Text(b"2251799813685248.0").apply_numeric_affinity(),
            Value::Integer(2251799813685248)
        );
        assert_eq!(
            Value::Text(b"-2251799813685248.0").apply_numeric_affinity(),
            Value::Integer(-2251799813685248)
        );
        assert_eq!(
            Value::Text(b"2251799813685249.0").apply_numeric_affinity(),
            Value::Real(2251799813685249.0)
        );
        assert_eq!(
            Value::Text(b"-2251799813685249.0").apply_numeric_affinity(),
            Value::Real(-2251799813685249.0)
        );

        // TODO; i64 overflow should preserve 15 digits?
        assert_eq!(
            Value::Text(b"9223372036854775808").apply_numeric_affinity(),
            Value::Real(9223372036854776e3)
        );
        assert_eq!(
            Value::Text(b"-9223372036854775809").apply_numeric_affinity(),
            Value::Real(-9223372036854776e3)
        );

        // Invalid text as numeric
        assert_eq!(
            Value::Text(b"12345a").apply_numeric_affinity(),
            Value::Text(b"12345a")
        );
        assert_eq!(
            Value::Text(b"12345e").apply_numeric_affinity(),
            Value::Text(b"12345e")
        );
        assert_eq!(
            Value::Text(b"a12345").apply_numeric_affinity(),
            Value::Text(b"a12345")
        );
        assert_eq!(
            Value::Text(b".").apply_numeric_affinity(),
            Value::Text(b".")
        );

        assert_eq!(
            Value::Blob(b"12345").apply_numeric_affinity(),
            Value::Blob(b"12345")
        );
    }

    #[test]
    fn test_apply_text_affinity() {
        assert_eq!(
            Value::Integer(12345).apply_text_affinity(&mut Vec::new()),
            Value::Text(b"12345")
        );
        assert_eq!(
            Value::Integer(-12345).apply_text_affinity(&mut Vec::new()),
            Value::Text(b"-12345")
        );
        assert_eq!(
            Value::Real(12345.1).apply_text_affinity(&mut Vec::new()),
            Value::Text(b"12345.1")
        );
        assert_eq!(
            Value::Real(-12345.1).apply_text_affinity(&mut Vec::new()),
            Value::Text(b"-12345.1")
        );
        assert_eq!(
            Value::Text(b"abcde").apply_text_affinity(&mut Vec::new()),
            Value::Text(b"abcde")
        );
        assert_eq!(
            Value::Blob(b"abcde").apply_text_affinity(&mut Vec::new()),
            Value::Text(b"abcde")
        );
    }

    #[test]
    fn test_apply_text_affinity_buffer() {
        let mut buf = Vec::new();
        Value::Integer(12345).apply_text_affinity(&mut buf);
        assert_eq!(buf.len(), 5);

        let mut buf = Vec::new();
        Value::Real(12345.1).apply_text_affinity(&mut buf);
        assert_eq!(buf.len(), 7);

        let mut buf = Vec::new();
        Value::Text(b"abcde").apply_text_affinity(&mut buf);
        assert_eq!(buf.capacity(), 0);

        let mut buf = Vec::new();
        Value::Blob(b"abcde").apply_text_affinity(&mut buf);
        assert_eq!(buf.capacity(), 0);
    }

    #[test]
    fn test_force_apply_type_affinity_numeric() {
        assert_eq!(
            Value::Null.force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Null
        );

        assert_eq!(
            Value::Integer(12345).force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Integer(12345)
        );

        assert_eq!(
            Value::Real(12345.1).force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Real(12345.1)
        );

        assert_eq!(
            Value::Text(b"12345").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b" 12345 ").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b"9223372036854775807").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Integer(9223372036854775807)
        );
        assert_eq!(
            Value::Text(b"-9223372036854775808").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Integer(-9223372036854775808)
        );
        assert_eq!(
            Value::Text(b"0.0").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Integer(0)
        );
        assert_eq!(
            Value::Text(b"12345.0").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b"12345.6").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Real(12345.6)
        );
        assert_eq!(
            Value::Text(b" 12345.6 ").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Real(12345.6)
        );
        assert_eq!(
            Value::Text(b"12345.6e+10").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Real(12345.6e10)
        );
        assert_eq!(
            Value::Text(b"12345e-1").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Real(1234.5)
        );
        assert_eq!(
            Value::Text(b"2251799813685248.0").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Integer(2251799813685248)
        );
        assert_eq!(
            Value::Text(b"-2251799813685248.0").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Integer(-2251799813685248)
        );
        assert_eq!(
            Value::Text(b"2251799813685249.0").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Real(2251799813685249.0)
        );
        assert_eq!(
            Value::Text(b"-2251799813685249.0").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Real(-2251799813685249.0)
        );

        // TODO; i64 overflow should preserve 15 digits?
        assert_eq!(
            Value::Text(b"9223372036854775808").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Real(9223372036854776e3)
        );
        assert_eq!(
            Value::Text(b"-9223372036854775809").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Real(-9223372036854776e3)
        );

        // Invalid text as numeric
        assert_eq!(
            Value::Text(b"9223372036854775807e").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Integer(9223372036854775807)
        );
        assert_eq!(
            Value::Text(b"9223372036854775807.e").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Real(9223372036854776e3)
        );
        assert_eq!(
            Value::Text(b"12345a").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b"12345e").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b"12345.e").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b"12345.6a").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Real(12345.6)
        );
        assert_eq!(
            Value::Text(b"12345.6e").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Real(12345.6)
        );
        assert_eq!(
            Value::Text(b"a12345").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Integer(0)
        );
        assert_eq!(
            Value::Text(b".").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Integer(0)
        );

        assert_eq!(
            Value::Blob(b"12345").force_apply_type_affinity(TypeAffinity::Numeric),
            Value::Integer(12345)
        );
    }

    #[test]
    fn test_force_apply_type_affinity_integer() {
        assert_eq!(
            Value::Null.force_apply_type_affinity(TypeAffinity::Integer),
            Value::Null
        );

        assert_eq!(
            Value::Integer(12345).force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(12345)
        );

        assert_eq!(
            Value::Real(12345.1).force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(12345)
        );

        assert_eq!(
            Value::Text(b"12345").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b"-12345").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(-12345)
        );
        assert_eq!(
            Value::Text(b"0012345").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b"-0012345").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(-12345)
        );
        assert_eq!(
            Value::Text(b"9223372036854775807").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(9223372036854775807)
        );
        assert_eq!(
            Value::Text(b"  0009223372036854775807")
                .force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(9223372036854775807)
        );
        assert_eq!(
            Value::Text(b"-9223372036854775808").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(-9223372036854775808)
        );
        assert_eq!(
            Value::Text(b"  -0009223372036854775808")
                .force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(-9223372036854775808)
        );
        assert_eq!(
            Value::Text(b"12345.6").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b"12345e-1").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b"12345.6e2").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b"9223372036854775808").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(9223372036854775807)
        );
        assert_eq!(
            Value::Text(b"-9223372036854775809").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(-9223372036854775808)
        );
        assert_eq!(
            Value::Text(b"12345a").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b"12345e").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b"12345a").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(12345)
        );
        assert_eq!(
            Value::Text(b"a12345").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(0)
        );
        assert_eq!(
            Value::Text(b"-+12345").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(0)
        );

        assert_eq!(
            Value::Blob(b"12345").force_apply_type_affinity(TypeAffinity::Integer),
            Value::Integer(12345)
        );
    }

    #[test]
    fn test_force_apply_type_affinity_real() {
        assert_eq!(
            Value::Null.force_apply_type_affinity(TypeAffinity::Real),
            Value::Null
        );

        assert_eq!(
            Value::Integer(12345).force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(12345.0)
        );
        assert_eq!(
            Value::Integer(9223372036854775807).force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(9223372036854776e3)
        );

        assert_eq!(
            Value::Real(12345.1).force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(12345.1)
        );

        assert_eq!(
            Value::Text(b"0.1").force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(0.1)
        );
        assert_eq!(
            Value::Text(b".1").force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(0.1)
        );
        assert_eq!(
            Value::Text(b"12345").force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(12345.0)
        );
        assert_eq!(
            Value::Text(b"12345.6").force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(12345.6)
        );
        assert_eq!(
            Value::Text(b"-12345.6").force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(-12345.6)
        );
        assert_eq!(
            Value::Text(b"0012345.6").force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(12345.6)
        );
        assert_eq!(
            Value::Text(b"-0012345.6").force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(-12345.6)
        );
        assert_eq!(
            Value::Text(b"12345.6e-1").force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(1234.56)
        );
        assert_eq!(
            Value::Text(b"12345e-1").force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(1234.5)
        );
        assert_eq!(
            Value::Text(b"9223372036854775808").force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(9223372036854776e3)
        );
        assert_eq!(
            Value::Text(b"12345a").force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(12345.0)
        );
        assert_eq!(
            Value::Text(b"a12345").force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(0.0)
        );
        assert_eq!(
            Value::Text(b"+-12345").force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(0.0)
        );

        assert_eq!(
            Value::Text(b"12345").force_apply_type_affinity(TypeAffinity::Real),
            Value::Real(12345.0)
        );
    }

    #[test]
    fn test_force_apply_type_affinity_text() {
        assert_eq!(
            Value::Null.force_apply_type_affinity(TypeAffinity::Text),
            Value::Null
        );
        // TODO; tests for integer/real
        assert_eq!(
            Value::Text(b"12345").force_apply_type_affinity(TypeAffinity::Text),
            Value::Text(b"12345")
        );
        assert_eq!(
            Value::Blob(b"12345").force_apply_type_affinity(TypeAffinity::Text),
            Value::Text(b"12345")
        );
    }

    #[test]
    fn test_force_apply_type_affinity_blob() {
        assert_eq!(
            Value::Null.force_apply_type_affinity(TypeAffinity::Blob),
            Value::Null
        );
        // TODO; tests for integer/real
        assert_eq!(
            Value::Text(b"12345").force_apply_type_affinity(TypeAffinity::Blob),
            Value::Blob(b"12345")
        );
        assert_eq!(
            Value::Blob(b"12345").force_apply_type_affinity(TypeAffinity::Blob),
            Value::Blob(b"12345")
        );
    }
}
