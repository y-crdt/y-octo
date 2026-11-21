#![no_main]

use libfuzzer_sys::fuzz_target;
use y_octo::{Doc, Update, diff_update_v1, encode_state_vector_from_update_v1, validate_update_v1};

const MAX_INPUT: usize = 64 << 10;

fn check_pair(update_bytes: &[u8], sv_bytes: &[u8]) {
    let valid = validate_update_v1(update_bytes).is_ok();
    let decoded = Update::decode_v1(update_bytes);
    assert_eq!(valid, decoded.is_ok());

    if let Ok(sv) = encode_state_vector_from_update_v1(update_bytes) {
        assert!(valid);
        let diff_self = diff_update_v1(update_bytes, &sv).expect("diff with own SV must succeed");
        assert!(validate_update_v1(&diff_self).is_ok());

        // When every client in `update_bytes` starts at 0 contiguously with no
        // gaps/Skips before real structs, applying it to a fresh Doc leaves no
        // pending updates and `diff(u, sv_of(u))` emits 0 struct clients.
        let mut doc = Doc::default();
        if doc.apply_update_from_binary_v1(update_bytes).is_ok()
            && !doc.has_pending_updates()
            && doc.get_state_vector().encode_v1().ok().as_deref() == Some(sv.as_slice())
        {
            assert_eq!(diff_self[0], 0);
        }
    }

    if let Ok(diff) = diff_update_v1(update_bytes, sv_bytes) {
        assert!(validate_update_v1(&diff).is_ok());
    }
}

fuzz_target!(|data: &[u8]| {
    if data.len() > MAX_INPUT {
        return;
    }

    // Exercise the full input against an empty state vector `[0]`.
    check_pair(data, &[0]);

    // Split `data` into arbitrary `(update_bytes, sv_bytes)` slices.
    if data.len() >= 2 {
        let rest = &data[2..];
        let split = (usize::from(data[0]) | (usize::from(data[1]) << 8)) % (rest.len() + 1);
        let (update_bytes, sv_bytes) = rest.split_at(split);
        check_pair(update_bytes, sv_bytes);
    }
});
