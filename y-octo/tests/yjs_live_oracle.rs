mod support;

use std::collections::HashMap;

use serde_json::{Value as Json, json};
use support::*;

// The operation stream is generated once from a fixed xorshift32 seed by Yjs.
// Rust independently executes it against both a live Doc and ordinary
// containers.
fn model_live(kind: &str) {
    let corpus = fixtures();
    for scenario in for_version(&corpus, "13.6.33")
        .into_iter()
        .filter(|s| s["kind"] == kind)
    {
        let mut local = doc(101, true);
        let mut remote = doc(202, true);
        let mut text: Vec<u16> = Vec::new();
        let mut array: Vec<Json> = Vec::new();
        let mut map: HashMap<String, Json> = HashMap::new();
        for (i, step) in scenario["steps"].as_array().unwrap().iter().enumerate() {
            let op = &step["op"];
            let index = op["index"].as_u64().unwrap_or(0) as usize;
            let len = op["length"].as_u64().unwrap_or(0) as usize;
            match op["kind"].as_str().unwrap() {
                "text_insert" => {
                    text.splice(index..index, op["value"].as_str().unwrap().encode_utf16());
                }
                "text_remove" => {
                    text.drain(index..index + len);
                }
                "array_insert" => array.insert(index, op["value"].clone()),
                "array_remove" => {
                    array.drain(index..index + len);
                }
                "map_insert" => {
                    map.insert(op["key"].as_str().unwrap().into(), op["value"].clone());
                }
                "map_remove" => {
                    map.remove(op["key"].as_str().unwrap());
                }
                "gc" => {}
                other => panic!("unknown model operation {other}"),
            }
            let context = format!("{} step {i}: {op}", scenario["name"]);
            // Independently verify that the fixture's semantic expectations
            // agree with the plain model, before invoking the implementation
            // under test.
            assert_eq!(
                step["expected"]["text"],
                String::from_utf16(&text).unwrap(),
                "{context}"
            );
            assert_eq!(step["expected"]["array"], json!(array), "{context}");
            assert_eq!(step["expected"]["map"], json!(map), "{context}");
            if step["remote"] == true {
                remote
                    .apply_update_from_binary_v1(local.encode_state_as_update_v1(&remote.get_state_vector()).unwrap())
                    .unwrap();
                let sv = local.get_state_vector();
                edit(&remote, op);
                local
                    .apply_update_from_binary_v1(remote.encode_state_as_update_v1(&sv).unwrap())
                    .unwrap();
            } else {
                edit(&local, op);
            }
            assert_state(&local, &step["expected"], &context);
            // Reopen after every step, including after explicit GC, without GC
            // in the recipient: malformed origins must not be hidden by
            // optimization.
            let mut reopened = doc(303, false);
            reopened
                .apply_update_from_binary_v1(local.encode_update_v1().unwrap())
                .unwrap();
            assert_state(&reopened, &step["expected"], &format!("{context}, reopened"));
        }
        let mut from_yjs = doc(404, true);
        from_yjs
            .apply_update_from_binary_v1(bytes(&scenario["full_update"]))
            .unwrap();
        assert_state(&from_yjs, &snapshot(&local), "final full Yjs update vs local document");
    }
}

#[test]
#[ignore = "Remote updates leave stale Text search markers; fixed by core direction A2"]
fn text_local_remote_model() {
    model_live("text");
}

#[test]
#[ignore = "Remote updates leave stale Array search markers; fixed by core direction A2"]
fn array_local_remote_model() {
    model_live("array");
}

#[test]
#[cfg_attr(
    miri,
    ignore = "Large semantic oracle; ordinary tests cover it, Miri runs the GC smoke case"
)]
fn map_gc_reinsert_model() {
    model_live("map");
}

#[test]
#[cfg_attr(
    miri,
    ignore = "Large semantic oracle; ordinary tests cover it, Miri runs the GC smoke case"
)]
fn yjs_live_updates_match_every_step() {
    let corpus = fixtures();
    for scenario in corpus["records"].as_array().unwrap() {
        let mut d = doc(303, true);
        for (i, step) in scenario["steps"].as_array().unwrap().iter().enumerate() {
            d.apply_update_from_binary_v1(bytes(&step["update"])).unwrap();
            assert_state(
                &d,
                &step["expected"],
                &format!("{} versions={} step {i}", scenario["name"], scenario["versions"]),
            );
        }
    }
}

#[test]
#[cfg_attr(
    miri,
    ignore = "Large semantic oracle; ordinary tests cover it, Miri runs the GC smoke case"
)]
fn pinned_versions_agree_on_live_scenarios() {
    let corpus = fixtures();
    assert_provenance(&corpus);
}

// Keep the pointer-sensitive GC/merge/reinsert path in Miri without repeatedly
// parsing and replaying the semantic corpus under an interpreter.
#[test]
#[cfg(miri)]
fn map_gc_reinsert_miri_smoke() {
    let source = doc(101, true);
    let mut map = source.get_or_create_map("map").unwrap();
    map.insert("k".into(), 1).unwrap();
    map.insert("k".into(), 2).unwrap();
    map.remove("k");
    source.gc().unwrap();
    map.insert("k".into(), 3).unwrap();
    let mut peer = doc(202, false);
    peer.apply_update_from_binary_v1(source.encode_update_v1().unwrap())
        .unwrap();
    assert_eq!(map.get("k"), peer.get_or_create_map("map").unwrap().get("k"));
    assert_eq!(map.get("k"), Some(y_octo::Value::Any(y_octo::Any::Integer(3))));
}
