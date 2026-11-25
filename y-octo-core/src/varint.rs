use alloc::vec::Vec;

use crate::CodecError;

/// Decodes an unsigned LEB128 varint up to 64 bits (max 10 bytes, 10th byte
/// carries at most 1 payload bit), matching
/// `y_octo::codec::integer::read_var_u64`.
#[inline]
pub fn decode_var_u64(input: &[u8]) -> Result<(u64, usize), CodecError> {
    let mut value = 0u64;
    let mut i = 0usize;
    while i < input.len() && i < 10 {
        let b = input[i];
        if i == 9 && b > 1 {
            return Err(CodecError::VarintOverflow);
        }
        let bits = (b & 0x7f) as u64;
        value |= bits << ((i * 7) as u32);
        i += 1;
        if (b & 0x80) == 0 {
            return Ok((value, i));
        }
    }
    if i == 10 {
        Err(CodecError::VarintOverflow)
    } else {
        Err(CodecError::UnexpectedEof)
    }
}

/// Encodes a `u64` into a stack-allocated LEB128 buffer without heap
/// allocation, returning `(buf, len)` with `1 <= len <= 10`.
pub fn encode_var_u64_buf(mut value: u64) -> ([u8; 10], usize) {
    let mut buf = [0u8; 10];
    let mut len = 0usize;
    while len < 9 && value >= 128 {
        buf[len] = ((value as u8) & 0x7f) | 0x80;
        len += 1;
        value >>= 7;
    }
    buf[len] = value as u8;
    len += 1;
    (buf, len)
}

/// Encodes a `u64` in lib0 unsigned varint format.
pub fn encode_var_u64(value: u64) -> Vec<u8> {
    let (buf, len) = encode_var_u64_buf(value);
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < len {
        out.push(buf[i]);
        i += 1;
    }
    out
}

/// Decodes a lib0 signed 32-bit varint together with its sign bit (so `-0` is
/// distinguishable from `+0`), matching `y_octo::codec::integer::read_var_i32`.
#[inline]
pub fn decode_var_i32_with_sign(input: &[u8]) -> Result<((i32, bool), usize), CodecError> {
    if input.is_empty() {
        return Err(CodecError::UnexpectedEof);
    }
    let first = input[0];
    let is_negative = (first & 0x40) != 0;
    let mut num = (first & 0x3f) as u64;
    let mut curr = first;
    let mut i = 1usize;
    let mut shift = 6u32;

    while (curr & 0x80) != 0 {
        if shift >= 32 {
            return Err(CodecError::VarintOverflow);
        }
        if i >= input.len() {
            return Err(CodecError::UnexpectedEof);
        }
        curr = input[i];
        num |= ((curr & 0x7f) as u64) << shift;
        shift += 7;
        i += 1;
    }

    let max_mag = if is_negative {
        (i32::MAX as u64) + 1
    } else {
        i32::MAX as u64
    };
    if num > max_mag {
        return Err(CodecError::VarintOverflow);
    }
    let val = if is_negative {
        if num == (i32::MAX as u64) + 1 {
            i32::MIN
        } else {
            -(num as i32)
        }
    } else {
        num as i32
    };
    Ok(((val, is_negative), i))
}

/// Decodes a lib0 signed 32-bit varint.
pub fn decode_var_i32(input: &[u8]) -> Result<(i32, usize), CodecError> {
    let ((val, _), len) = decode_var_i32_with_sign(input)?;
    Ok((val, len))
}

/// Encodes an `i32` into a stack-allocated lib0 signed varint buffer without
/// heap allocation, returning `(buf, len)` with `1 <= len <= 5`.
pub fn encode_var_i32_buf(value: i32) -> ([u8; 5], usize) {
    let mut buf = [0u8; 5];
    let is_negative = value < 0;
    let mut num = if is_negative {
        if value == i32::MIN {
            (i32::MAX as u64) + 1
        } else {
            (-value) as u64
        }
    } else {
        value as u64
    };

    let first_more = if num > 0x3f { 0x80u8 } else { 0u8 };
    let first_sign = if is_negative { 0x40u8 } else { 0u8 };
    buf[0] = first_more | first_sign | ((num as u8) & 0x3f);
    let mut len = 1usize;
    num >>= 6;
    while len < 5 && num > 0 {
        let more = if num > 0x7f { 0x80u8 } else { 0u8 };
        buf[len] = more | ((num as u8) & 0x7f);
        len += 1;
        num >>= 7;
    }
    (buf, len)
}

/// Encodes an `i32` in lib0 signed varint format.
pub fn encode_var_i32(value: i32) -> Vec<u8> {
    let (buf, len) = encode_var_i32_buf(value);
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < len {
        out.push(buf[i]);
        i += 1;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_u64() {
        for v in [0u64, 1, 127, 128, 16383, 16384, (1 << 53) - 1, u64::MAX / 2, u64::MAX] {
            let mut enc = encode_var_u64(v);
            enc.extend_from_slice(&[0xaa, 0xbb]);
            let (dec, used) = decode_var_u64(&enc).unwrap();
            assert_eq!(dec, v);
            assert_eq!(used, enc.len() - 2);
        }
    }

    #[test]
    fn roundtrip_i32() {
        for v in [0i32, 1, -1, 63, -63, 64, -64, i32::MAX, i32::MIN] {
            let mut enc = encode_var_i32(v);
            enc.push(0x99);
            let (dec, used) = decode_var_i32(&enc).unwrap();
            assert_eq!(dec, v);
            assert_eq!(used, enc.len() - 1);
        }
        assert_eq!(decode_var_i32_with_sign(&[0x40]), Ok(((0, true), 1)));
    }
}
