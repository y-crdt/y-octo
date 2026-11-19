//! Byte-addressed edit/delivery traces shared by libFuzzer and the pinned Yjs
//! differential test. Shrinking removes byte records, never invents invalid
//! numeric indices: sequence positions are symbolic and lengths are clamped.
use serde_json::{Value as Json, json};
pub fn from_bytes(bytes: &[u8]) -> Json {
    let seed = bytes
        .iter()
        .fold(1_u32, |s, b| s.wrapping_mul(16777619) ^ u32::from(*b))
        .max(1);
    if bytes.first().is_some_and(|byte| byte & 7 == 7) {
        return typed_packets(bytes, seed);
    }
    let mut steps = Vec::new();
    for at in 0..3 {
        steps.push(json!({"op":"create","at":at,"target":["map"],"key":"parent","kind":"map"}));
        for (key, kind) in [("t", "text"), ("a", "array"), ("m", "map")] {
            steps.push(json!({"op":"create","at":at,"target":["map","parent"],"key":key,"kind":kind}));
        }
    }
    for record in bytes.chunks(6).take(48) {
        let n = |i: usize| record.get(i).copied().unwrap_or(0) as usize;
        let at = n(0) % 3;
        let pos = ["begin", "middle", "end"][n(3) % 3];
        let nested = n(2) % 2 == 1;
        let target = |kind, key| {
            if nested {
                json!(["map", "parent", key])
            } else {
                json!([kind])
            }
        };
        let key = ["k", "x", "y"][n(4) % 3];
        let value = match n(5) % 4 {
            0 => json!(n(4)),
            1 => json!(["opaque", true]),
            2 => json!({"ref":n(4)}),
            _ => json!(false),
        };
        steps.push(match n(1)%10 {
            0|1=>json!({"op":"text_insert","at":at,"target":target("text","t"),"index":pos,"value":(["a","界","😀","NOP"][n(4)%4])}),
            2=>json!({"op":"text_remove","at":at,"target":target("text","t"),"index":pos,"length":1+n(4)%3}),
            3=>json!({"op":"array_insert","at":at,"target":target("array","a"),"index":pos,"value":value}),
            4=>json!({"op":"array_remove","at":at,"target":target("array","a"),"index":pos,"length":1+n(4)%3}),
            5=>json!({"op":"map_insert","at":at,"target":target("map","m"),"key":key,"value":value}),
            6=>json!({"op":"map_remove","at":at,"target":target("map","m"),"key":key}),
            7=>json!({"op":"format","at":at,"target":target("text","t"),"index":pos,"length":1+n(4)%3,"attributes":{"bold":n(5)%2==1}}),
            8=>json!({"op":"text_embed","at":at,"target":target("text","t"),"index":pos,"value":{"ref":n(4)}}),
            _=>json!({"op":"gc","at":at}),
        });
    }
    // Parent deletion follows local editing so every target remains defined.
    for at in 0..3 {
        if bytes.get(at).is_some_and(|b| b & 0x80 != 0) {
            steps.push(json!({"op":"map_remove","at":at,"target":["map"],"key":"parent"}));
            steps.push(json!({"op":"gc","at":at}));
        }
    }
    // Deliver queued network updates after local index edits.
    for (i, b) in bytes.iter().take(12).enumerate() {
        let from = i % 3;
        let to = (from + 1 + (*b as usize % 2)) % 3;
        steps
            .push(json!({"op":"sync","from":from,"to":to,"updates":"all","reverse":b&1!=0,"repeat":1+(*b as usize%3)}));
    }
    for from in 0..3 {
        for to in 0..3 {
            if from != to {
                steps.push(json!({"op":"sync","from":from,"to":to,"updates":"all"}));
            }
        }
    }
    json!({"schema":1,"name":format!("fuzz-trajectory-{seed}"),"seed":seed,"replicas":[101,202,303],"roots":{"text":"text","array":"array","map":"map"},"steps":steps})
}
// Native Text/XML APIs cannot expose these typed embeds yet. The pinned
// Yjs wire fixture verifies content/type/identity online; this branch checks
// packet ordering, duplication, pending state, SV/DS and codec/reopen
// properties.
fn typed_packets(bytes: &[u8], seed: u32) -> Json {
    let corpus = crate::support::read_gzip_jsonl(include_bytes!("../../../src/fixtures/yjs-legacy.jsonl.gz"));
    let fixture = corpus["records"]
        .as_array()
        .unwrap()
        .iter()
        .find(|record| record["name"] == "text-type-embeds")
        .unwrap();
    let packets = fixture["packets"].as_array().unwrap();
    let mut order: Vec<_> = (0..packets.len()).collect();
    let offset = bytes.get(1).copied().unwrap_or(0) as usize % order.len();
    order.rotate_left(offset);
    if bytes.get(2).is_some_and(|byte| byte & 1 != 0) {
        order.reverse();
    }
    let mut steps = Vec::new();
    for index in order {
        steps.push(json!({"op":"apply","at":0,"update":packets[index]}));
    }
    for byte in bytes.iter().take(48) {
        steps.push(json!({"op":"apply","at":0,"update":packets[*byte as usize % packets.len()]}));
    }
    for to in [1, 2] {
        steps.push(json!({"op":"sync","from":0,"to":to,"updates":"all","repeat":2}));
    }
    json!({"schema":1,"name":format!("typed-embed-packets-{seed}"),"seed":seed,"replicas":[101,202,303],"roots":{},"wire_roots":{"typed_text":"text"},"packet_fixture":"text-type-embeds","steps":steps})
}
pub fn seeds() -> Vec<Vec<u8>> {
    let mut seeds = vec![
        Vec::new(),
        vec![7, 0, 0],
        vec![7, 5, 1, 255, 31],
        vec![
            128, 129, 130, 2, 9, 3, 1, 0, 1, 0, 0, 0, 2, 3, 1, 2, 255, 2, 0, 7, 1, 0, 5, 1, 1, 8, 1, 1, 7, 0,
        ],
        (0..20).flat_map(|i| [i % 3, i % 10, i % 2, i % 3, i, i % 4]).collect(),
    ];
    for seed in 1..=12 {
        let mut random = super::generate::Random::new(seed);
        seeds.push((0..144).map(|_| random.next(256) as u8).collect());
    }
    seeds
}

/// Fixed-wire online verifier declares the real Text/XmlText roots and compares
/// recursively typed content/item IDs, outside the generic editable-root API.
pub fn verify_legacy(cases: &Json) -> Result<(), String> {
    use std::{
        io::Write,
        process::{Command, Stdio},
    };
    let mut child = Command::new("node")
        .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/oracle/legacy.mjs"))
        .arg("--verify")
        .stdin(Stdio::piped())
        .spawn()
        .map_err(|e| e.to_string())?;
    serde_json::to_writer(child.stdin.as_mut().unwrap(), cases).map_err(|e| e.to_string())?;
    child.stdin.take().unwrap().flush().map_err(|e| e.to_string())?;
    if child.wait().map_err(|e| e.to_string())?.success() {
        Ok(())
    } else {
        Err("pinned Yjs rejected legacy wire".into())
    }
}
