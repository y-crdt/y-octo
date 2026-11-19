mod support;
use serde_json::{Value as Json, json};
use y_octo::{Any, Doc, TextAttributes, TextDeltaOp, TextInsert, TypeIdentity};

fn state(sv: &y_octo::StateVector) -> Vec<(u64, u64)> {
    let mut pairs: Vec<_> = sv.iter().map(|(c, k)| (*c, *k)).collect();
    pairs.sort();
    pairs
}

fn case(map_parent: bool) -> (Doc, Json) {
    let doc = support::doc(101, true);
    let mut published = doc.get_or_create_text("text").unwrap();
    published.insert(0, "A").unwrap();
    let prefix = doc.encode_update_v1().unwrap();
    let sv = doc.get_state_vector();
    let original_ids = published.identity_runs().unwrap();
    let position = published.relative_position(0, 0).unwrap();
    let mut child = doc.create_map().unwrap();
    let mut items = doc.create_array().unwrap();
    let mut text = doc.create_text().unwrap();
    text.apply_delta(&[TextDeltaOp::Insert {
        insert: TextInsert::Text("A😀Z".into()),
        format: Some(TextAttributes::from([("bold".into(), Any::True)])),
    }])
    .unwrap();
    text.remove(1, 2).unwrap();
    items.push(text.clone()).unwrap();
    items.push(99).unwrap();
    items.remove(1, 1).unwrap();
    child.insert("items".into(), items.clone()).unwrap();
    child.insert("value".into(), 0).unwrap();
    child.insert("value".into(), 7).unwrap();
    assert_eq!(text.to_string(), "AZ");
    assert_eq!(items.len(), 1);
    assert_eq!(doc.get_state_vector(), sv);
    assert_eq!(doc.encode_update_v1().unwrap(), prefix);
    assert!(text.identity().is_err());
    assert!(text.identity_runs().is_err());
    assert_eq!(items.id(), None);
    assert_eq!(child.id(), None);
    if map_parent {
        doc.get_or_create_map("map")
            .unwrap()
            .insert("child".into(), child.clone())
            .unwrap();
    } else {
        doc.get_or_create_array("array").unwrap().push(child.clone()).unwrap();
    }
    assert_eq!(published.identity_runs().unwrap(), original_ids);
    assert_eq!(published.relative_position(0, 0).unwrap(), position);
    // These handles predate two staging mounts and the final document mount.
    text.insert(2, "!").unwrap();
    items.push(8).unwrap();
    child.insert("extra".into(), 9).unwrap();
    published.insert(1, "B").unwrap();
    let text_id = match text.identity().unwrap() {
        TypeIdentity::Item(id) => id,
        _ => unreachable!(),
    };
    let id = |id: y_octo::Id| json!([id.client, id.clock]);
    let expected = json!({"items":["AZ!",8],"value":7,"extra":9});
    let root = if map_parent { "map" } else { "array" };
    let path = if map_parent { json!(["child"]) } else { json!([0]) };
    let payload = json!({
        "root":root, "child_path":path,
        "expected": if map_parent { json!({"child":expected}) } else { json!([expected]) },
        "prefix":support::trace::encode_hex(&prefix),
        "full":support::trace::encode_hex(&doc.encode_update_v1().unwrap()),
        "diff":support::trace::encode_hex(&doc.encode_state_as_update_v1(&sv).unwrap()),
        "sv": state(&doc.get_state_vector()),
        "ids":[id(child.id().unwrap()),id(items.id().unwrap()),id(text_id)],
        "delta":serde_json::to_value(text.to_delta()).unwrap(),
    });
    (doc, payload)
}

#[test]
fn preliminary_full_and_incremental_updates_reopen() {
    for map in [false, true] {
        let (doc, c) = case(map);
        for updates in [
            vec![&c["full"]],
            vec![&c["prefix"], &c["diff"], &c["diff"]],
            vec![&c["diff"], &c["prefix"]],
        ] {
            let mut peer = support::doc(202, true);
            for u in updates {
                peer.apply_update_from_binary_v1(support::bytes(u)).unwrap();
            }
            assert!(!peer.has_pending_updates());
            assert_eq!(peer.get_state_vector(), doc.get_state_vector());
            let actual = if map {
                serde_json::to_value(peer.get_or_create_map("map").unwrap()).unwrap()
            } else {
                serde_json::to_value(peer.get_or_create_array("array").unwrap()).unwrap()
            };
            assert_eq!(actual, c["expected"]);
            assert_eq!(peer.get_or_create_text("text").unwrap().to_string(), "AB");
            // Received roots and nested types acquire the same permanent
            // publication state as locally mounted and rebuilt types.
            let nested = if map {
                let root = peer.get_or_create_map("map").unwrap();
                assert!(root.identity().is_ok());
                root.get("child").unwrap().to_map().unwrap()
            } else {
                let root = peer.get_or_create_array("array").unwrap();
                assert!(root.identity().is_ok());
                root.get(0).unwrap().to_map().unwrap()
            };
            assert!(nested.identity().is_ok());
            let items = nested.get("items").unwrap().to_array().unwrap();
            assert!(items.identity().is_ok());
            let mut text = items.get(0).unwrap().to_text().unwrap();
            assert!(text.identity().is_ok());
            text.insert(3, "?").unwrap();
            assert_eq!(peer.get_state_vector().get(&202), 1);
            assert_eq!(text.to_string(), "AZ!?");
        }
    }
}

#[test]
#[ignore = "Requires Node and npm ci --prefix y-octo/tests/oracle"]
fn online_preliminary_yjs_roundtrip() {
    use std::{
        io::Write,
        process::{Command, Stdio},
    };
    let cases: Vec<_> = [false, true].map(|map| case(map).1).into();
    let mut child = Command::new("node")
        .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/oracle/detached.mjs"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    serde_json::to_writer(child.stdin.as_mut().unwrap(), &cases).unwrap();
    child.stdin.take().unwrap().flush().unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    let responses: Vec<Json> = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(responses.len(), 8);
    for r in responses {
        let c = cases.iter().find(|c| c["root"] == r["root"]).unwrap();
        let mut peer = support::doc(303, true);
        peer.apply_update_from_binary_v1(support::bytes(&r["update"])).unwrap();
        assert!(!peer.has_pending_updates());
        assert_eq!(json!(state(&peer.get_state_vector())), c["sv"]);
        let actual = if r["root"] == "map" {
            serde_json::to_value(peer.get_or_create_map("map").unwrap()).unwrap()
        } else {
            serde_json::to_value(peer.get_or_create_array("array").unwrap()).unwrap()
        };
        assert_eq!(actual, c["expected"]);
    }
}
