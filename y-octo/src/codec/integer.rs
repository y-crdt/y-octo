use std::io::{Error, Write};

use byteorder::WriteBytesExt;
use nom::Needed;

use super::*;

pub fn read_var_u64(input: &[u8]) -> IResult<&[u8], u64> {
    match y_octo_core::varint::decode_var_u64(input) {
        Ok((num, used)) => Ok((&input[used..], num)),
        Err(y_octo_core::CodecError::UnexpectedEof) => Err(nom::Err::Incomplete(Needed::new(input.len() + 1))),
        Err(_) => Err(nom::Err::Failure(nom::error::Error::new(
            input,
            nom::error::ErrorKind::TooLarge,
        ))),
    }
}

pub fn write_var_u64<W: Write>(buffer: &mut W, num: u64) -> Result<(), Error> {
    let (bytes, len) = y_octo_core::varint::encode_var_u64_buf(num);
    buffer.write_all(&bytes[..len])
}

pub fn read_var_i32(input: &[u8]) -> IResult<&[u8], i32> {
    match y_octo_core::varint::decode_var_i32(input) {
        Ok((num, used)) => Ok((&input[used..], num)),
        Err(y_octo_core::CodecError::UnexpectedEof) => Err(nom::Err::Incomplete(Needed::new(input.len() + 1))),
        Err(_) => Err(nom::Err::Failure(nom::error::Error::new(
            input,
            nom::error::ErrorKind::TooLarge,
        ))),
    }
}

pub fn write_var_i32<W: Write>(buffer: &mut W, num: i32) -> Result<(), Error> {
    let (bytes, len) = y_octo_core::varint::encode_var_i32_buf(num);
    buffer.write_all(&bytes[..len])
}

/// Largest JavaScript safe integer supported by this signed varInt codec.
pub const MAX_SAFE_INTEGER: i64 = (1_i64 << 53) - 1;

/// Decode a lib0 signed varInt within JavaScript's safe integer range.
pub fn read_var_i64(input: &[u8]) -> IResult<&[u8], i64> {
    let Some(&first) = input.first() else {
        return Err(nom::Err::Incomplete(Needed::new(1)));
    };
    let negative = first & 0x40 != 0;
    let mut num = (first & 0x3f) as i64;
    let mut current = first;
    let mut shift = 6;
    let mut rest = &input[1..];
    while current & 0x80 != 0 {
        if shift >= 53 {
            return Err(nom::Err::Failure(nom::error::Error::new(
                input,
                nom::error::ErrorKind::TooLarge,
            )));
        }
        let Some(&next) = rest.first() else {
            return Err(nom::Err::Incomplete(Needed::new(input.len() + 1)));
        };
        current = next;
        num |= ((current & 0x7f) as i64) << shift;
        shift += 7;
        rest = &rest[1..];
    }
    if num > MAX_SAFE_INTEGER {
        return Err(nom::Err::Failure(nom::error::Error::new(
            input,
            nom::error::ErrorKind::TooLarge,
        )));
    }
    Ok((rest, if negative { -num } else { num }))
}

/// Encode a lib0 signed varInt within JavaScript's safe integer range.
pub fn write_var_i64<W: Write>(buffer: &mut W, num: i64) -> Result<(), Error> {
    if !(-MAX_SAFE_INTEGER..=MAX_SAFE_INTEGER).contains(&num) {
        return Err(Error::new(
            std::io::ErrorKind::InvalidInput,
            "signed varint exceeds JavaScript safe integer range",
        ));
    }
    let negative = num < 0;
    let mut magnitude = num.unsigned_abs();
    buffer.write_u8(
        (if magnitude > 0x3f { 0x80 } else { 0 }) | (if negative { 0x40 } else { 0 }) | (magnitude as u8 & 0x3f),
    )?;
    magnitude >>= 6;
    while magnitude > 0 {
        buffer.write_u8((if magnitude > 0x7f { 0x80 } else { 0 }) | (magnitude as u8 & 0x7f))?;
        magnitude >>= 7;
    }
    Ok(())
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::CrdtReader;

    fn test_var_uint_enc_dec(num: u64) {
        let mut buf = Vec::new();
        write_var_u64(&mut buf, num).unwrap();

        let (rest, decoded_num) = read_var_u64(&buf).unwrap();
        assert_eq!(num, decoded_num);
        assert_eq!(rest.len(), 0);
        assert_eq!(crate::RawDecoder::new(&buf).read_var_u64().unwrap(), num);
    }

    fn test_var_int_enc_dec(num: i32) {
        {
            let mut buf = Vec::new();
            write_var_i32(&mut buf, num).unwrap();

            let (rest, decoded_num) = read_var_i32(&buf).unwrap();
            assert_eq!(num, decoded_num);
            assert_eq!(rest.len(), 0);
        }
    }

    #[test]
    fn test_var_uint_rejects_overflow_alias() {
        let input = [129, 128, 128, 128, 128, 128, 128, 128, 128, 2];
        let decoded = read_var_u64(&input);
        assert!(decoded.is_err(), "overflow aliased to {decoded:?}");
        assert!(crate::RawDecoder::new(&input).read_var_u64().is_err());
        assert!(read_var_u64(&[128; 11]).is_err());
    }

    #[test]
    fn test_var_int_rejects_overflow_alias() {
        // +2^31, -(2^31 + 1), and 2^32 must not alias i32 values.
        for input in [
            vec![128, 128, 128, 128, 16],
            vec![193, 128, 128, 128, 16],
            vec![128, 128, 128, 128, 32],
            vec![129, 128, 128, 128, 128, 128, 128, 128, 128, 4],
        ] {
            assert!(read_var_i32(&input).is_err(), "{input:?}");
            assert!(crate::RawDecoder::new(&input).read_var_i32().is_err());
        }
    }

    #[test]
    fn test_update_rejects_overflow_client_and_clock() {
        use crate::{ReadDoc, Update};
        let overflow = [129, 128, 128, 128, 128, 128, 128, 128, 128, 2];
        for clock in [false, true] {
            // One GC struct of length 1, followed by an empty delete set.
            let mut update = vec![1, 1];
            if clock {
                update.push(1);
            }
            update.extend(overflow);
            if !clock {
                update.push(0);
            }
            update.extend([0, 1, 0]);
            assert!(Update::decode_v1(&update).is_err());
            assert!(ReadDoc::from_full_update_v1(update.as_slice()).is_err());
        }
    }

    #[test]
    fn test_safe_signed_varint_yjs_bytes() {
        use crate::{CrdtWriter, RawDecoder, RawEncoder};
        // lib0 writeVarInt / Yjs wire fixtures, including values beyond i32.
        for (value, bytes) in [
            (1_i64 << 31, vec![128, 128, 128, 128, 16]),
            (-(1_i64 << 31) - 1, vec![193, 128, 128, 128, 16]),
            (MAX_SAFE_INTEGER, vec![191, 255, 255, 255, 255, 255, 255, 31]),
            (-MAX_SAFE_INTEGER, vec![255, 255, 255, 255, 255, 255, 255, 31]),
        ] {
            let mut encoded = Vec::new();
            write_var_i64(&mut encoded, value).unwrap();
            assert_eq!(encoded, bytes);
            assert_eq!(read_var_i64(&bytes).unwrap(), (&[][..], value));
            let mut encoder = RawEncoder::default();
            encoder.write_var_i64(value).unwrap();
            assert_eq!(encoder.into_inner(), bytes);
            assert_eq!(RawDecoder::new(&bytes).read_var_i64().unwrap(), value);
        }
    }

    #[test]
    fn test_safe_signed_varint_zero_and_overflow() {
        use crate::{CrdtWriter, RawDecoder, RawEncoder};
        assert_eq!(read_var_i64(&[64]).unwrap(), (&[][..], 0));
        assert_eq!(RawDecoder::new(&[64]).read_var_i64().unwrap(), 0);
        let mut encoder = RawEncoder::default();
        encoder.write_var_i64(0).unwrap();
        assert_eq!(encoder.into_inner(), [0]);
        let mut bytes = Vec::new();
        write_var_i64(&mut bytes, 0).unwrap();
        assert_eq!(bytes, [0]);
        for value in [MAX_SAFE_INTEGER + 1, -MAX_SAFE_INTEGER - 1, i64::MIN, i64::MAX] {
            let mut bytes = Vec::new();
            assert!(write_var_i64(&mut bytes, value).is_err());
            assert!(bytes.is_empty());
            let mut encoder = RawEncoder::default();
            assert!(encoder.write_var_i64(value).is_err());
            assert!(encoder.into_inner().is_empty());
        }
        for first in [128, 192] {
            let bytes = [first, 128, 128, 128, 128, 128, 128, 32];
            assert!(read_var_i64(&bytes).is_err());
            assert!(RawDecoder::new(&bytes).read_var_i64().is_err());
        }
        assert!(read_var_i64(&[128; 9]).is_err());
    }

    #[test]
    fn test_var_uint_codec() {
        test_var_uint_enc_dec(0);
        test_var_uint_enc_dec(1);
        test_var_uint_enc_dec(127);
        test_var_uint_enc_dec(0b1000_0000);
        test_var_uint_enc_dec(0b1_0000_0000);
        test_var_uint_enc_dec(0b1_1111_1111);
        test_var_uint_enc_dec(0b10_0000_0000);
        test_var_uint_enc_dec(0b11_1111_1111);
        test_var_uint_enc_dec(0x7fff_ffff_ffff_ffff);
        test_var_uint_enc_dec(u64::MAX);
        test_var_uint_enc_dec((1_u64 << 53) - 1);
    }

    #[test]
    fn test_var_int() {
        test_var_int_enc_dec(0);
        test_var_int_enc_dec(1);
        test_var_int_enc_dec(-1);
        test_var_int_enc_dec(63);
        test_var_int_enc_dec(-63);
        test_var_int_enc_dec(64);
        test_var_int_enc_dec(-64);
        test_var_int_enc_dec(i32::MAX);
        test_var_int_enc_dec(i32::MIN);
        test_var_int_enc_dec(((1 << 20) - 1) * 8);
        test_var_int_enc_dec(-((1 << 20) - 1) * 8);
    }

    #[test]
    fn test_var_int_decode_malformed_no_panic() {
        // sign bit set and enough continuation bytes for wrapping_shl to set
        // bit 63, making the accumulated i64 value i64::MIN before negation
        let mut input = vec![0b1100_0000];
        input.extend([0b1000_0000; 8]);
        input.push(0b0000_0010);
        assert!(read_var_i32(&input).is_err());

        // unterminated continuation bytes
        assert!(read_var_i32(&[0b1111_1111; 16]).is_err());
    }
}
