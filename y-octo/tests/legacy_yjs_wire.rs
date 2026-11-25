mod support;
use serde_json::{Value as Json, json};
use y_octo::{Doc, Update, read_var_i32, read_var_i64, read_var_u64, write_var_i32, write_var_i64, write_var_u64};
fn corpus() -> Json {
    support::read_gzip_jsonl(include_bytes!("../src/fixtures/yjs-legacy.jsonl.gz"))
}
fn decode(bytes: impl AsRef<[u8]>, fixture: &Json) -> Doc {
    let mut doc = support::doc(303, true);
    for (name, kind) in fixture["roots"].as_object().unwrap() {
        match kind.as_str().unwrap() {
            "Text" => {
                doc.get_or_create_text(name).unwrap();
            }
            "Map" => {
                doc.get_or_create_map(name).unwrap();
            }
            "Array" => {
                doc.get_or_create_array(name).unwrap();
            }
            // Exact XmlText root declarations are covered in the private
            // document unit test; the public API intentionally has none.
            _ => {}
        }
    }
    doc.apply_update_from_binary_v1(bytes).unwrap();
    doc
}
fn mixed() -> Doc {
    let doc = support::doc(101, true);
    let mut a = doc.get_or_create_array("abc").unwrap();
    for value in [
        y_octo::Any::from(42),
        y_octo::Any::from(-42),
        y_octo::Any::True,
        y_octo::Any::False,
        y_octo::Any::from("hello"),
        y_octo::Any::from("world"),
    ] {
        a.push(value).unwrap();
    }
    let mut child = doc.create_array().unwrap();
    a.push(child.clone()).unwrap();
    child.push(1).unwrap();
    doc
}
#[test]
fn pinned_yjs_legacy_updates_remain_applicable() {
    let fixtures = corpus();
    support::assert_provenance(&fixtures);
    for fixture in fixtures["records"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|r| r["kind"] == "update")
    {
        let name = fixture["name"].as_str().unwrap();
        let bytes = support::bytes(&fixture["update"]);
        let doc = decode(&bytes, fixture);
        assert!(!doc.has_pending_updates(), "{name}");
        let encoded = doc.encode_update_v1().unwrap();
        let peer = decode(&encoded, fixture);
        assert!(!peer.has_pending_updates(), "{name}");
        assert_eq!(peer.get_state_vector(), doc.get_state_vector(), "{name}");
        assert_eq!(
            Update::decode_v1(&encoded).unwrap().encode_v1().unwrap(),
            encoded,
            "{name}"
        );
    }
    let doc = mixed();
    let array = doc.get_or_create_array("abc").unwrap();
    assert_eq!(
        serde_json::to_value(array).unwrap(),
        fixtures["records"]
            .as_array()
            .unwrap()
            .iter()
            .find(|r| r["name"] == "mixed-array")
            .unwrap()["expected"]["abc"]
    );
}
#[test]
fn signed_and_unsigned_codec_matches_pinned_lib0() {
    let integers = support::read_gzip_jsonl(include_bytes!("../src/fixtures/yjs-integers.jsonl.gz"));
    assert_eq!(integers["versions"], json!(["13.6.21", "13.6.33"]));
    let records = integers["records"].as_array().unwrap();
    let len = records.len();
    for (idx, v) in records.iter().enumerate() {
        if cfg!(miri) && idx >= 8 && idx + 8 < len && idx % 16 != 0 {
            continue;
        }
        let value = v[0].as_i64().unwrap();
        let signed = support::bytes(&v[1]);
        let unsigned = support::bytes(&v[2]);
        assert_eq!(read_var_i64(&signed).unwrap(), (&[][..], value));
        let mut bytes = Vec::new();
        write_var_i64(&mut bytes, value).unwrap();
        assert_eq!(bytes, signed);
        if let Ok(value) = i32::try_from(value) {
            assert_eq!(read_var_i32(&signed).unwrap(), (&[][..], value));
            let mut bytes = Vec::new();
            write_var_i32(&mut bytes, value).unwrap();
            assert_eq!(bytes, signed);
        }
        assert_eq!(read_var_u64(&unsigned).unwrap(), (&[][..], value.unsigned_abs()));
        let mut bytes = Vec::new();
        write_var_u64(&mut bytes, value.unsigned_abs()).unwrap();
        assert_eq!(bytes, unsigned);
    }
}
#[test]
#[ignore = "Requires Node and npm ci --prefix y-octo/tests/oracle"]
fn online_legacy_yjs_roundtrip() {
    use std::{
        io::Write,
        process::{Command, Stdio},
    };
    let mut cases = Vec::new();
    for fixture in corpus()["records"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|r| r["kind"] == "update")
    {
        let name = fixture["name"].as_str().unwrap();
        let doc = decode(support::bytes(&fixture["update"]), fixture);
        cases.push(json!({"name":name,"update":support::trace::encode_hex(&doc.encode_update_v1().unwrap())}));
    }
    cases.push(json!({"name":"mixed-array","update":support::trace::encode_hex(&mixed().encode_update_v1().unwrap())}));
    let mut child = Command::new("node")
        .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/oracle/legacy.mjs"))
        .arg("--verify")
        .stdin(Stdio::piped())
        .spawn()
        .unwrap();
    serde_json::to_writer(child.stdin.as_mut().unwrap(), &cases).unwrap();
    child.stdin.take().unwrap().flush().unwrap();
    assert!(child.wait().unwrap().success());
}
