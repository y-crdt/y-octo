#![no_main]
use libfuzzer_sys::fuzz_target;
use y_octo::{CrdtReader, CrdtWriter, RawDecoder, RawEncoder, read_var_i32, write_var_i32};
fuzz_target!(|data: Vec<i32>| {
    for value in data {
        let mut bytes = Vec::new();
        write_var_i32(&mut bytes, value).unwrap();
        assert_eq!(read_var_i32(&bytes).unwrap(), (&[][..], value));
        let mut encoder = RawEncoder::default();
        encoder.write_var_i32(value).unwrap();
        assert_eq!(encoder.into_inner(), bytes);
        assert_eq!(RawDecoder::new(&bytes).read_var_i32().unwrap(), value);
    }
});
