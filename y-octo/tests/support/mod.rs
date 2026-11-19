#![allow(dead_code)]
pub mod concurrent;
use serde_json::{Value as Json, json};
use y_octo::{Doc, DocOptions, StateVector, Update};

pub fn doc(client: u64, gc: bool) -> Doc {
    DocOptions {
        client_id: client,
        guid: format!("oracle-{client}"),
        gc,
    }
    .build()
}

pub fn fixtures() -> Json {
    read_gzip_jsonl(include_bytes!("../oracle/live.jsonl.gz"))
}

pub fn read_gzip_jsonl(input: &[u8]) -> Json {
    use std::io::Read;
    let mut text = String::new();
    flate2::read::GzDecoder::new(input).read_to_string(&mut text).unwrap();
    read_jsonl(&text)
}

pub fn read_jsonl(input: &str) -> Json {
    let mut lines = input.lines();
    let mut corpus: Json = serde_json::from_str(lines.next().unwrap()).unwrap();
    corpus["records"] = Json::Array(lines.map(|line| serde_json::from_str(line).unwrap()).collect());
    corpus
}

pub fn for_version<'a>(corpus: &'a Json, version: &str) -> Vec<&'a Json> {
    corpus["records"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|record| record["versions"].as_array().unwrap().iter().any(|v| v == version))
        .collect()
}

pub fn assert_provenance(corpus: &Json) {
    assert_eq!(corpus["schema"], 2);
    assert_eq!(corpus["authoritative_version"], "13.6.33");
    let differences = corpus["version_differences"].as_array().unwrap();
    let records = corpus["records"].as_array().unwrap();
    let mut seen = std::collections::BTreeSet::new();
    for record in records {
        let versions = record["versions"].as_array().unwrap();
        let divergent = differences.contains(&record["name"]);
        assert_eq!(
            versions.len(),
            if divergent { 1 } else { 2 },
            "{} version provenance",
            record["name"]
        );
        for version in versions {
            assert!([json!("13.6.21"), json!("13.6.33")].contains(version));
            assert!(
                seen.insert((record["name"].as_str().unwrap(), version.as_str().unwrap())),
                "duplicate version/case"
            );
        }
    }
    for record in records {
        for version in ["13.6.21", "13.6.33"] {
            assert!(
                seen.contains(&(record["name"].as_str().unwrap(), version)),
                "{} missing {version}",
                record["name"]
            );
        }
    }
}

pub fn bytes(value: &Json) -> Vec<u8> {
    let hex = value.as_str().unwrap();
    assert_eq!(hex.len() % 2, 0, "wire hex must contain complete bytes");
    hex.as_bytes()
        .chunks_exact(2)
        .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
        .collect()
}

// The fixture authors are fixed, including updates still waiting on
// dependencies. A ceiling SV strips all structs but preserves both integrated
// and pending delete ranges in the wire update, so neither gets silently
// omitted.
fn oracle_ceiling() -> StateVector {
    StateVector::from([(101, u64::MAX), (202, u64::MAX), (303, u64::MAX), (404, u64::MAX)])
}

pub fn snapshot(d: &Doc) -> Json {
    let text = d.get_or_create_text("text").unwrap();
    let array = d.get_or_create_array("array").unwrap();
    let map = d.get_or_create_map("map").unwrap();
    let mut delta = serde_json::to_value(text.to_delta()).unwrap();
    for op in delta.as_array_mut().unwrap() {
        if let Some(attrs) = op.as_object_mut().unwrap().remove("format")
            && !attrs.as_object().unwrap().is_empty()
        {
            op["attributes"] = attrs;
        }
    }
    let mut sv: Vec<_> = d.get_state_vector().iter().map(|(c, k)| (*c, *k)).collect();
    sv.sort_unstable();
    // Read the canonical wire delete set, not store-local deletion tracking:
    // incoming ContentDeleted/GC structs need not populate that local tracker.
    let mut update = Update::decode_v1(d.encode_state_as_update_v1(&oracle_ceiling()).unwrap()).unwrap();
    let mut grouped = std::collections::BTreeMap::<u64, Vec<(u64, u64)>>::new();
    for (client, range) in update.delete_set_iter(oracle_ceiling()) {
        grouped
            .entry(client)
            .or_default()
            .push((range.start, range.end - range.start));
    }
    let ds: Vec<_> = grouped
        .into_iter()
        .map(|(client, mut ranges)| {
            ranges.sort_unstable();
            (client, ranges)
        })
        .collect();
    json!({"text":text.to_string(),"delta":delta,"array":serde_json::to_value(array).unwrap(),
        "map":serde_json::to_value(map).unwrap(),"state_vector":sv,"delete_set":ds})
}

pub fn assert_state(d: &Doc, expected: &Json, context: &str) {
    assert_eq!(snapshot(d), *expected, "{context}");
}

pub fn edit(d: &Doc, op: &Json) {
    let index = op["index"].as_u64().unwrap_or(0);
    let len = op["length"].as_u64().unwrap_or(0);
    match op["kind"].as_str().unwrap() {
        "text_insert" => d
            .get_or_create_text("text")
            .unwrap()
            .insert(index, op["value"].as_str().unwrap())
            .unwrap(),
        "text_remove" => d.get_or_create_text("text").unwrap().remove(index, len).unwrap(),
        "array_insert" => d
            .get_or_create_array("array")
            .unwrap()
            .insert(index, op["value"].as_i64().unwrap())
            .unwrap(),
        "array_remove" => d.get_or_create_array("array").unwrap().remove(index, len).unwrap(),
        "map_insert" => d
            .get_or_create_map("map")
            .unwrap()
            .insert(op["key"].as_str().unwrap().into(), op["value"].as_i64().unwrap())
            .unwrap(),
        "map_remove" => d.get_or_create_map("map").unwrap().remove(op["key"].as_str().unwrap()),
        "gc" => d.gc().unwrap(),
        other => panic!("unknown operation {other}"),
    }
}
