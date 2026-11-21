use std::{
    io::Write,
    path::Path,
    process::{Command, Stdio},
};

use serde_json::{Value as Json, json};
use y_octo::{
    AHashMap, Any, Doc, DocOptions, HashMapExt, TextAttributes, TextDeltaOp, TextInsert, UndoManager, UndoOptions,
    Value,
};

fn decode_hex(hex: &str) -> Vec<u8> {
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
        .collect()
}

fn encode_hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        use std::fmt::Write as _;
        let _ = write!(out, "{b:02x}");
    }
    out
}

fn summarize_tree(values: impl IntoIterator<Item = Value>) -> Vec<Json> {
    values
        .into_iter()
        .map(|v| match v {
            Value::XMLElement(el) => json!({
                "kind": "XMLElement",
                "tag": el.tag_name(),
                "attrs": el.attributes().into_iter().map(|(k, _)| k).collect::<Vec<_>>(),
            }),
            Value::XMLText(txt) => json!({
                "kind": "XMLText",
                "text": txt.to_xml_string(),
            }),
            Value::XMLHook(hook) => {
                let mut entries: Vec<(String, Json)> = hook
                    .entries()
                    .map(|(k, v)| (k, serde_json::to_value(v).unwrap()))
                    .collect();
                entries.sort_by(|a, b| a.0.cmp(&b.0));
                json!({
                    "kind": "XMLHook",
                    "hookName": hook.hook_name(),
                    "entries": entries,
                })
            }
            Value::XMLFragment(_) => json!({ "kind": "XMLFragment" }),
            _ => json!({ "kind": "Unknown" }),
        })
        .collect()
}

fn assert_case1_matches(expected: &Json) {
    let update = decode_hex(expected["update_hex"].as_str().unwrap());
    let doc = Doc::try_from_binary_v1_with_options(&update, DocOptions::from_identity(505, "case1".into())).unwrap();

    let frag = doc.get_or_create_xml_fragment("xml").unwrap();
    let mixed = doc.get_or_create_xml_fragment("mixed").unwrap();
    let root_el = doc.get_or_create_xml_element("rootEl").unwrap();

    assert_eq!(frag.to_xml_string(), expected["frag_to_string"].as_str().unwrap());
    assert_eq!(mixed.to_xml_string(), expected["mixed_to_string"].as_str().unwrap());
    assert_eq!(mixed.to_xml_string(), "p12false<b>ok</b>");
    assert_eq!(root_el.to_xml_string(), expected["root_el_to_string"].as_str().unwrap());
    assert_eq!(root_el.tag_name(), expected["root_el_node_name"].as_str().unwrap());

    let div = frag.first_child().unwrap().to_xml_element().unwrap();
    let actual_attr_keys: Vec<String> = div.attributes().into_iter().map(|(k, _)| k).collect();
    let expected_attr_keys: Vec<String> = expected["div_attrs_keys"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_str().unwrap().to_string())
        .collect();
    assert_eq!(actual_attr_keys, expected_attr_keys);

    assert_eq!(Json::Array(summarize_tree(frag.tree_walker())), expected["tree_walker"]);

    let mut sv: Vec<(u64, u64)> = doc.get_state_vector().iter().map(|(&c, &clk)| (c, clk)).collect();
    sv.sort_by_key(|(c, _)| *c);
    assert_eq!(json!(sv), expected["state_vector"]);

    // Re-encode from y-octo and verify round-trip stability.
    let reencoded = doc.encode_update_v1().unwrap();
    let reopened =
        Doc::try_from_binary_v1_with_options(&reencoded, DocOptions::from_identity(606, "case1-reopen".into()))
            .unwrap();
    assert_eq!(
        reopened.get_or_create_xml_fragment("xml").unwrap().to_xml_string(),
        expected["frag_to_string"].as_str().unwrap()
    );
}

#[test]
#[cfg_attr(miri, ignore = "Oracle JSON fixture; ordinary tests cover it")]
fn yjs_13_6_33_xml_case1_offline_fixture() {
    let expected: Json = serde_json::from_str(include_str!("oracle/xml.json")).unwrap();
    assert_case1_matches(&expected);
}

#[test]
#[ignore = "Requires Node and npm ci --prefix y-octo/tests/oracle"]
fn online_yjs_13_6_33_xml_bidirectional_oracle() {
    let oracle_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/oracle");
    assert!(
        oracle_dir.join("node_modules/yjs-13-6-33").exists(),
        "missing yjs-13-6-33 oracle dependency: run npm ci --prefix y-octo/tests/oracle"
    );
    let script = oracle_dir.join("xml.mjs");

    // Case 1: Yjs 13.6.33 -> y-octo
    let out = Command::new("node")
        .arg(&script)
        .arg("--case1")
        .output()
        .expect("run node xml.mjs --case1");
    assert!(
        out.status.success(),
        "xml.mjs --case1 failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let expected_case1: Json = serde_json::from_slice(&out.stdout).unwrap();
    assert_case1_matches(&expected_case1);

    // Case 2: y-octo (preliminary mount, attr overwrite/delete, rich text,
    // XMLHook, Undo/Redo) -> Yjs 13.6.33
    let doc = DocOptions::from_identity(707, "case2".into()).build();
    let mut frag = doc.get_or_create_xml_fragment("xml").unwrap();
    let mut root_el = doc.get_or_create_xml_element("rootEl").unwrap();
    root_el.set_attribute("id", "root-1").unwrap();

    let undo = UndoManager::<()>::new(
        &doc,
        [(&frag).into()],
        UndoOptions {
            capture_timeout: 0,
            ..UndoOptions::default()
        },
    )
    .unwrap();

    // Build preliminary XML subtree before mounting
    let mut section = doc.create_xml_element("Section").unwrap();
    section.set_attribute("class", "draft").unwrap();
    section.set_attribute("count", 1).unwrap();
    section.set_attribute("obsolete", "bye").unwrap();
    section.set_attribute("flag", Any::Null).unwrap();
    section.set_attribute("f_exp_neg", 1e-7_f64).unwrap();
    section.set_attribute("f_fix_neg", 1e-6_f64).unwrap();
    section.set_attribute("f_fix_pos", 1e20_f64).unwrap();
    section.set_attribute("f_exp_pos", 1e21_f64).unwrap();
    section
        .set_attribute("f_tie_pos", f64::from_bits(0x430c6bf526340002))
        .unwrap();
    section
        .set_attribute("f_tie_neg", -f64::from_bits(0x430c6bf526340002))
        .unwrap();
    section.set_attribute("f_neg_zero", -0.0_f64).unwrap();
    section.set_attribute("\u{E000}", "bmp-pua").unwrap();
    section.set_attribute("\u{10000}", "supplementary").unwrap();

    let mut text = doc.create_xml_text().unwrap();
    let mut link_obj = AHashMap::new();
    link_obj.insert("href".to_string(), Any::String("https://a.test?x=1&y=2".into()));
    link_obj.insert("title".to_string(), Any::String("A & B".into()));
    let arr11 = Any::Array((0..11).map(Any::Integer).collect());
    text.apply_delta(&[
        TextDeltaOp::Insert {
            insert: TextInsert::Text("Hello <world> & \"friends\"!".into()),
            format: Some(TextAttributes::from([
                ("bold".into(), Any::True),
                ("link".into(), Any::Object(Box::new(link_obj))),
            ])),
        },
        TextDeltaOp::Insert {
            insert: TextInsert::Text(" tail".into()),
            format: None,
        },
        TextDeltaOp::Insert {
            insert: TextInsert::Text("X".into()),
            format: Some(TextAttributes::from([
                ("link".into(), Any::String("ab".into())),
                (
                    "arr".into(),
                    Any::Array(vec![Any::String("x".into()), Any::Integer(12)]),
                ),
                ("arr11".into(), arr11),
                ("bin".into(), Any::Binary(vec![7, 8])),
            ])),
        },
    ])
    .unwrap();
    section.push(text.clone()).unwrap();

    let mut hook = doc.create_xml_hook("custom-embed").unwrap();
    hook.insert("k".into(), "v").unwrap();
    hook.insert("n".into(), 9).unwrap();

    // Mount preliminary subtree + hook
    frag.push(section.clone()).unwrap();
    frag.push(hook.clone()).unwrap();

    // Overwrite and remove attributes, edit rich text
    section.set_attribute("class", "published").unwrap();
    section.remove_attribute("obsolete").unwrap();
    text.format(27, 4, TextAttributes::from([("italic".into(), Any::True)]))
        .unwrap();

    // Undo and redo the last two steps
    let before_undo = frag.to_xml_string();
    assert!(undo.undo().unwrap().is_some());
    assert!(undo.undo().unwrap().is_some());
    assert_ne!(frag.to_xml_string(), before_undo);
    assert!(undo.redo().unwrap().is_some());
    assert!(undo.redo().unwrap().is_some());
    assert_eq!(frag.to_xml_string(), before_undo);

    // Send V1 update to Yjs 13.6.33 and verify exact equality
    let update = doc.encode_update_v1().unwrap();
    let payload = json!({ "update_hex": encode_hex(&update) });
    let mut child = Command::new("node")
        .arg(&script)
        .arg("--verify")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn node xml.mjs --verify");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(payload.to_string().as_bytes())
        .unwrap();
    let verify_out = child.wait_with_output().unwrap();
    assert!(
        verify_out.status.success(),
        "xml.mjs --verify failed: {}",
        String::from_utf8_lossy(&verify_out.stderr)
    );
    let yjs_result: Json = serde_json::from_slice(&verify_out.stdout).unwrap();

    assert_eq!(frag.to_xml_string(), yjs_result["frag_to_string"].as_str().unwrap());
    assert_eq!(
        root_el.to_xml_string(),
        yjs_result["root_el_to_string"].as_str().unwrap()
    );
    assert_eq!(root_el.tag_name(), yjs_result["root_el_node_name"].as_str().unwrap());
    assert_eq!(
        Json::Array(summarize_tree(frag.tree_walker())),
        yjs_result["tree_walker"]
    );
    let mut sv: Vec<(u64, u64)> = doc.get_state_vector().iter().map(|(&c, &clk)| (c, clk)).collect();
    sv.sort_by_key(|(c, _)| *c);
    assert_eq!(json!(sv), yjs_result["state_vector"]);
}
