use serde_json::{Value as Json, json};
use y_octo::{TextInsert, TypeIdentity, Value};

use super::*;

pub fn fixtures() -> Json {
    read_gzip_jsonl(include_bytes!("../oracle/concurrent.jsonl.gz"))
}

fn delta(text: &y_octo::Text) -> Json {
    let mut ops = serde_json::to_value(text.to_delta()).unwrap();
    for op in ops.as_array_mut().unwrap() {
        if let Some(attrs) = op.as_object_mut().unwrap().remove("format")
            && !attrs.as_object().unwrap().is_empty()
        {
            op["attributes"] = attrs;
        }
    }
    ops
}

// Check type discriminants as well as JSON. Distinct nested Map/Array
// identities are observable through the current public API; root types have no
// item ID.
fn assert_shape(actual: Value, expected: &Json, context: &str) {
    match (actual, expected["kind"].as_str().unwrap()) {
        (Value::Any(v), "any") => assert_eq!(serde_json::to_value(v).unwrap(), expected["value"], "{context}"),
        (Value::Text(t), "text") => {
            let id = match t.identity().unwrap() {
                TypeIdentity::Item(id) => json!([id.client, id.clock]),
                TypeIdentity::Root(_) => Json::Null,
            };
            assert_eq!(id, expected["id"], "{context}");
            let mut identities = Vec::new();
            for run in t.identity_runs().unwrap() {
                if let TextInsert::Text(text) = run.insert {
                    identities.extend(
                        text.encode_utf16()
                            .enumerate()
                            .map(|(offset, ch)| json!([run.id.client, run.id.clock + offset as u64, ch])),
                    );
                } else {
                    panic!("unexpected embed in string-only fixture");
                }
            }
            assert_eq!(json!(identities), expected["visible_identities"], "{context}");
            assert_eq!(t.to_string(), expected["value"], "{context}");
            assert_eq!(delta(&t), expected["delta"], "{context}");
        }
        (Value::Array(a), "array") => {
            assert_eq!(
                a.id().map(|id| json!([id.client, id.clock])).unwrap_or(Json::Null),
                expected["id"],
                "{context}"
            );
            assert_eq!(
                a.len() as usize,
                expected["value"].as_array().unwrap().len(),
                "{context}"
            );
            // Read a snapshot without populating the live indexed search cache.
            // Indexed edits and their invalidation are exercised in the live
            // model.
            let values: Vec<_> = a.iter().collect();
            for (actual, v) in values.into_iter().zip(expected["value"].as_array().unwrap()) {
                assert_shape(actual, v, context);
            }
        }
        (Value::Map(m), "map") => {
            assert_eq!(
                m.id().map(|id| json!([id.client, id.clock])).unwrap_or(Json::Null),
                expected["id"],
                "{context}"
            );
            assert_eq!(
                m.len() as usize,
                expected["value"].as_object().unwrap().len(),
                "{context}"
            );
            for (key, v) in expected["value"].as_object().unwrap() {
                assert_shape(m.get(key).unwrap(), v, context);
            }
        }
        (actual, kind) => panic!("{context}: expected {kind}, got {actual:?}"),
    }
}

pub fn assert_snapshot(d: &y_octo::Doc, expected: &Json, context: &str) {
    let mut plain = expected.clone();
    plain.as_object_mut().unwrap().remove("structure");
    assert_state(d, &plain, context);
    assert_shape(
        Value::Text(d.get_or_create_text("text").unwrap()),
        &expected["structure"]["text"],
        context,
    );
    assert_shape(
        Value::Array(d.get_or_create_array("array").unwrap()),
        &expected["structure"]["array"],
        context,
    );
    assert_shape(
        Value::Map(d.get_or_create_map("map").unwrap()),
        &expected["structure"]["map"],
        context,
    );
}
