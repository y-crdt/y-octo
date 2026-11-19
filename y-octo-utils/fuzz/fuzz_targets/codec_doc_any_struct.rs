#![no_main]

use libfuzzer_sys::fuzz_target;
use y_octo::{Any, CrdtRead, CrdtWrite, RawDecoder, RawEncoder};

fn roundtrip(any: Any) {
    let mut buffer = RawEncoder::default();
    if let Err(e) = any.write(&mut buffer) {
        panic!("Failed to write message: {:?}, {:?}", any, e);
    }
    if let Ok(any2) = Any::read(&mut RawDecoder::new(&buffer.into_inner())) {
        assert_eq!(any, any2);
    }
}

fuzz_target!(|data: Vec<(String, Any)>| {
    // Keys must be derived from the fuzz input as well; pulling them from a
    // thread-local rng makes runs non-deterministic and crashes irreproducible.
    roundtrip(Any::Object(Box::new(data.iter().cloned().collect())));
    roundtrip(Any::Array(data.into_iter().map(|(_, value)| value).collect()));
});
