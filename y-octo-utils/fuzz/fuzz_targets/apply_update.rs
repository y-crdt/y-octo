#![no_main]
use libfuzzer_sys::fuzz_target;
// Test-only trace interpreter, also exercised against both pinned Yjs versions.
// No Yjs process or reference engine runs in the hot fuzzing loop.
#[path = "../../../y-octo/tests/support/mod.rs"]
mod support;
fuzz_target!(|bytes: &[u8]| {
    let trace = support::trace::trajectory::from_bytes(bytes);
    let seed = trace["seed"].as_u64().unwrap() as u32;
    if let Err(error) = support::trace::generate::update_properties(&trace, seed) {
        let saved = support::trace::generate::regression(&trace, &error, seed);
        panic!("{error}\n{}", support::trace::save_failure(&saved, "fuzz-trajectory"));
    }
});
