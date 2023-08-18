#![no_main]

use lib0::encoding::Write;
use libfuzzer_sys::fuzz_target;
use y_octo::{read_var_i64, write_var_i64};

fuzz_target!(|data: Vec<i64>| {
    for i in data {
        if i == i64::MIN {
            continue;
        }

        let mut buf1 = Vec::new();
        write_var_i64(&mut buf1, i).unwrap();

        let mut buf2 = Vec::new();
        buf2.write_var(i);

        assert_eq!(read_var_i64(&buf1).unwrap().1, i);
        assert_eq!(read_var_i64(&buf2).unwrap().1, i);
    }
});
