//! Replays `oracle/local.mjs`: a Yjs renderer's update applied with
//! [Doc::apply_local_update] after remote updates that wait for its structs,
//! then native undo/redo, checked step by step against Yjs. The online test
//! sends the native undo/redo updates back to the pinned Yjs renderers.

mod support;

use serde_json::{Value as Json, json};
use support::{concurrent::assert_snapshot, *};
use y_octo::{Doc, LocalUpdate, Origin, UndoManager, UndoOptions, Update};

fn corpus() -> Json {
    read_gzip_jsonl(include_bytes!("oracle/local.jsonl.gz"))
}

fn update(value: &Json) -> Update {
    Update::decode_v1(bytes(value)).unwrap()
}

/// Replays `scenario`, checking every step; returns the native updates the
/// renderer received, as hex (the first one is the sync after the local
/// update).
fn replay(scenario: &Json) -> Vec<String> {
    let context = format!("{} {}", scenario["name"], scenario["versions"]);
    let native = support::doc(101, true);
    let mut text = native.get_or_create_text("text").unwrap();
    let map = native.get_or_create_map("map").unwrap();
    native.get_or_create_array("array").unwrap();
    text.insert(0, "base").unwrap();

    #[derive(Clone, PartialEq, Eq, Hash)]
    struct Renderer;
    let renderer = Origin::new(Renderer);
    let undo = UndoManager::<()>::new(
        &native,
        [(&text).into(), (&map).into()],
        UndoOptions {
            capture_timeout: u64::MAX,
            tracked_origins: vec![Some(renderer.clone())],
        },
    )
    .unwrap();
    undo.advance_time(1);

    // the remote updates arrive first and wait for the renderer's structs
    for name in ["remote", "deletion"] {
        native
            .apply_update_with_origin(update(&scenario[name]), Origin::new("remote"))
            .unwrap();
    }
    assert!(native.has_pending_updates(), "{context}");
    assert_eq!(text.to_string(), "base", "{context}: nothing applied yet");

    let steps = scenario["steps"].as_array().unwrap();
    assert_eq!(
        native.apply_local_update(update(&scenario["local"]), renderer).unwrap(),
        LocalUpdate::Applied,
        "{context}"
    );
    assert!(!native.has_pending_updates(), "{context}");
    assert_snapshot(&native, &steps[0]["native"], &format!("{context}: apply"));

    // follows the native document like the Yjs renderer (another client ID:
    // it only receives)
    let mut replica = support::doc(99, true);
    replica.apply_update(update(&scenario["initial"])).unwrap();
    replica.apply_update(update(&scenario["local"])).unwrap();
    let mut sent = Vec::new();
    let mut send = |native: &Doc, replica: &mut Doc| {
        let update = native.encode_state_as_update_v1(&replica.get_state_vector()).unwrap();
        replica.apply_update_from_binary_v1(&update).unwrap();
        sent.push(support::trace::encode_hex(&update));
    };
    send(&native, &mut replica);

    for step in &steps[1..] {
        let context = format!("{context}: {}", step["op"]);
        let performed = match step["op"].as_str().unwrap() {
            "undo" => undo.undo().unwrap().is_some(),
            "redo" => undo.redo().unwrap().is_some(),
            op => panic!("unknown step {op}"),
        };
        assert_eq!(json!(performed), step["performed"], "{context}");
        assert_eq!(json!(undo.can_undo()), step["can_undo"], "{context}");
        assert_eq!(json!(undo.can_redo()), step["can_redo"], "{context}");
        assert_snapshot(&native, &step["native"], &context);
        send(&native, &mut replica);
        assert_snapshot(&replica, &step["renderer"], &format!("{context}: renderer"));
        // the renderer has nothing of its own to send back
        assert_eq!(replica.get_state_vector(), native.get_state_vector(), "{context}: echo");
        assert_eq!(step["echo"], 0, "{context}");
    }
    sent
}

#[test]
#[cfg_attr(miri, ignore = "Semantic oracle; ordinary tests cover it")]
fn yjs_renderer_updates_enter_the_native_history() {
    let corpus = corpus();
    assert_provenance(&corpus);
    for scenario in corpus["records"].as_array().unwrap() {
        replay(scenario);
    }
}

#[test]
#[ignore = "Requires Node and npm ci --prefix y-octo/tests/oracle"]
fn online_yjs_renderer_reads_native_undo() {
    use std::{
        io::Write,
        process::{Command, Stdio},
    };
    let corpus = corpus();
    let mut cases = Vec::new();
    for scenario in corpus["records"].as_array().unwrap() {
        let updates = replay(scenario);
        for version in scenario["versions"].as_array().unwrap() {
            cases.push(json!({"version": version, "updates": updates}));
        }
    }
    let mut child = Command::new("node")
        .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/oracle/local.mjs"))
        .arg("--verify")
        .stdin(Stdio::piped())
        .spawn()
        .unwrap();
    serde_json::to_writer(child.stdin.as_mut().unwrap(), &cases).unwrap();
    child.stdin.take().unwrap().flush().unwrap();
    assert!(child.wait().unwrap().success());
}
