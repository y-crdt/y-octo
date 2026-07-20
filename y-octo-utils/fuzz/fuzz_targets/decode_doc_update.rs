#![no_main]

use libfuzzer_sys::fuzz_target;
use y_octo::Doc;

fuzz_target!(|data: &[u8]| {
    // Feed arbitrary (possibly malformed) bytes to the most exposed entry point:
    // decoding an untrusted yjs update into a doc. Decoding must never panic,
    // and a successfully decoded doc must always re-encode without panicking.
    //
    // Malformed inputs can integrate into corrupt states whose encoding is
    // rejected on re-apply or serialized in a different (still valid) order,
    // so byte-level roundtrip stability is intentionally not asserted here;
    // canonical roundtrips of well-formed docs are covered by the
    // differential apply_update target.
    if let Ok(doc) = Doc::try_from_binary_v1(data) {
        let binary = doc.encode_update_v1().unwrap();
        if let Ok(doc2) = Doc::try_from_binary_v1(&binary) {
            let _ = doc2.encode_update_v1().unwrap();
        }
    }
});
