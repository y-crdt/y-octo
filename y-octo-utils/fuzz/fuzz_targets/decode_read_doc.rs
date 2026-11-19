#![no_main]

use libfuzzer_sys::fuzz_target;
use y_octo::{ReadDoc, ReadLimits};

fuzz_target!(|data: &[u8]| {
    let limits = ReadLimits {
        max_input_bytes: 1 << 20,
        max_structs: 10_000,
        max_clients: 1_000,
        max_collection_entries: 50_000,
        max_any_depth: 32,
        max_content_bytes: 1 << 20,
    };
    if data.len() <= limits.max_input_bytes {
        let _ = ReadDoc::from_full_update_v1_with_limits(data, limits);
    }
});
