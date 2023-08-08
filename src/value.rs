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

use std::io::Write;

// TODO: Own the buffer of Text and Blob.
#[derive(Debug, PartialEq)]
pub enum Value<'a> {
    Null,
    Integer(i64),
    Real(f64),
    Blob(&'a [u8]),
    // NOTE: Any text is not guaranteed to be valid UTF-8.
    Text(&'a [u8]),
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
}
