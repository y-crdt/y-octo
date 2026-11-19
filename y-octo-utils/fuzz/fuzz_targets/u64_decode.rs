#![no_main]
use libfuzzer_sys::fuzz_target;
use y_octo::{read_var_u64, write_var_u64};
// Decode arbitrary external bytes, including truncated and overflowing varints.
fuzz_target!(|input: &[u8]| {
    let mut bytes = input;
    while !bytes.is_empty() {
        let Ok((rest, value)) = read_var_u64(bytes) else { break };
        assert!(rest.len() < bytes.len());
        let mut canonical = Vec::new();
        write_var_u64(&mut canonical, value).unwrap();
        assert_eq!(read_var_u64(&canonical).unwrap(), (&[][..], value));
        bytes = rest;
    }
});
