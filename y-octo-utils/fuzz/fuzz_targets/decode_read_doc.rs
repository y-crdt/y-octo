#![no_main]

use libfuzzer_sys::fuzz_target;
use y_octo::{ReadDoc, ReadLimits, ReadValue};

/// Values visited per document, so deep or wide documents cannot time out.
const MAX_VISITS: usize = 4_096;

/// Reads every value reachable from the roots; the read API must never panic
/// on whatever a decoded snapshot contains.
fn project(doc: &ReadDoc) {
    let mut pending = Vec::new();
    for name in doc.root_names() {
        if let Some(map) = doc.map(name) {
            pending.push(ReadValue::Map(map));
        }
        if let Some(array) = doc.array(name) {
            pending.push(ReadValue::Array(array));
        }
        if let Some(text) = doc.text(name) {
            pending.push(ReadValue::Text(text));
        }
    }

    let mut visits = 0;
    while let Some(value) = pending.pop() {
        visits += 1;
        if visits > MAX_VISITS {
            return;
        }
        match value {
            ReadValue::Any(any) => {
                let _ = any.to_owned();
            }
            ReadValue::Map(map) => {
                let _ = map.len();
                for (key, value) in map.iter() {
                    let _ = map.get(key);
                    pending.push(value);
                }
            }
            ReadValue::Array(array) => {
                let _ = array.len();
                pending.extend(array.iter());
            }
            ReadValue::Text(text) => {
                let _ = text.to_string();
                let _ = text.runs().count();
            }
            ReadValue::Xml { map, array, .. } => {
                pending.push(ReadValue::Map(map));
                pending.push(ReadValue::Array(array));
            }
            ReadValue::Doc { options, .. } => {
                let _ = options.to_owned();
            }
        }
    }
}

fuzz_target!(|data: &[u8]| {
    let limits = ReadLimits {
        max_input_bytes: 1 << 20,
        max_structs: 10_000,
        max_clients: 1_000,
        max_collection_entries: 50_000,
        max_any_depth: 32,
        max_content_bytes: 1 << 20,
    };
    if data.len() <= limits.max_input_bytes
        && let Ok(doc) = ReadDoc::from_full_update_v1_with_limits(data, limits)
    {
        project(&doc);
    }
});
