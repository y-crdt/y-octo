#![no_main]

use libfuzzer_sys::fuzz_target;
use y_octo::{Doc, Value};

/// Larger inputs mostly slow the fuzzer down without reaching new paths.
const MAX_INPUT: usize = 64 << 10;
/// Values visited per projection, so deep or wide documents cannot time out.
const MAX_VISITS: usize = 4_096;

/// Reads every value reachable from `roots` through the mutable document API,
/// which must never panic on whatever the updates integrated.
fn project(roots: Vec<Value>) {
    let mut pending = roots;
    let mut visits = 0;
    while let Some(value) = pending.pop() {
        visits += 1;
        if visits > MAX_VISITS {
            return;
        }
        let _ = value.to_string();
        match value {
            // walked here instead of serialized: serialization recurses
            // once per nesting level
            Value::Map(map) => pending.extend(map.iter().map(|(_, value)| value)),
            Value::Array(array) => pending.extend(array.iter()),
            Value::Text(text) => {
                let _ = text.to_string();
                let _ = text.to_delta();
            }
            Value::Doc(doc) => {
                let _ = doc.guid();
            }
            _ => {}
        }
    }
}

fn roots(doc: &Doc, selector: u8) -> Vec<Value> {
    let mut roots = Vec::new();
    for name in doc.keys() {
        // Unknown roots take the kind of their first accessor; vary it.
        let value = match selector % 3 {
            0 => doc.get_or_create_map(&name).map(Value::Map),
            1 => doc.get_or_create_array(&name).map(Value::Array),
            _ => doc.get_or_create_text(&name).map(Value::Text),
        };
        if let Ok(value) = value {
            roots.push(value);
        }
    }
    roots
}

fuzz_target!(|data: &[u8]| {
    // Feed arbitrary (possibly malformed) bytes to the most exposed entry
    // point: decoding untrusted yjs updates into a doc, as a snapshot and as
    // two consecutive increments. Decoding and reading the result must never
    // panic, and a successfully decoded doc must always re-encode without
    // panicking.
    //
    // Malformed inputs can integrate into corrupt states whose encoding is
    // rejected on re-apply or serialized in a different (still valid) order,
    // so byte-level roundtrip stability is intentionally not asserted here;
    // canonical roundtrips of well-formed docs are covered by the
    // differential apply_update target.
    if data.len() > MAX_INPUT {
        return;
    }

    if let Ok(doc) = Doc::try_from_binary_v1(data) {
        project(roots(&doc, data.first().copied().unwrap_or_default()));
        let binary = doc.encode_update_v1().unwrap();
        if let Ok(doc2) = Doc::try_from_binary_v1(&binary) {
            let _ = doc2.encode_update_v1().unwrap();
        }
    }

    // The first byte picks where the input splits into two updates applied in
    // order, reaching overlap, pending and deletion paths across updates.
    if let Some((split, rest)) = data.split_first()
        && !rest.is_empty()
    {
        let (first, second) = rest.split_at(*split as usize % rest.len());
        let mut doc = Doc::default();
        let _ = doc.apply_update_from_binary_v1(first);
        let _ = doc.apply_update_from_binary_v1(second);
        project(roots(&doc, *split / 3));
        let _ = doc.encode_update_v1().unwrap();
    }
});
