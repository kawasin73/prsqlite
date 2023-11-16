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

/// The interface for payload.
pub trait Payload<E> {
    fn size(&self) -> PayloadSize;
    fn load(&self, offset: usize, buf: &mut [u8]) -> Result<usize, E>;
}

pub trait LocalPayload<E>: Payload<E> {
    fn buf(&self) -> &[u8];
}

pub struct SlicePayload<'a> {
    buf: &'a [u8],
    size: PayloadSize,
}

impl<'a> SlicePayload<'a> {
    #[allow(dead_code)]
    pub fn new(buf: &'a [u8]) -> anyhow::Result<Self> {
        let size = PayloadSize::try_from(buf.len() as u64)
            .map_err(|_| anyhow::anyhow!("payload size too large"))?;
        Ok(Self { buf, size })
    }
}

impl Payload<()> for SlicePayload<'_> {
    fn size(&self) -> PayloadSize {
        self.size
    }

    fn load(&self, offset: usize, buf: &mut [u8]) -> std::result::Result<usize, ()> {
        assert!(offset <= self.buf.len());
        let n = buf.len().min(self.buf.len() - offset);
        buf[..n].copy_from_slice(&self.buf[offset..offset + n]);
        Ok(n)
    }
}

impl LocalPayload<()> for SlicePayload<'_> {
    fn buf(&self) -> &[u8] {
        self.buf
    }
}

/// This is to guarantee that payload size is less than or equal to 2147483647
/// (= i32::MAX).
#[derive(Clone, Copy, Debug)]
pub struct PayloadSize(u32);

impl PayloadSize {
    #[inline]
    pub fn get(&self) -> u32 {
        self.0
    }
}

impl TryFrom<u64> for PayloadSize {
    type Error = ();

    fn try_from(value: u64) -> std::result::Result<Self, Self::Error> {
        // The maximum payload length is 2147483647 (= i32::MAX).
        if value <= i32::MAX as u64 {
            Ok(Self(value as u32))
        } else {
            Err(())
        }
    }
}
