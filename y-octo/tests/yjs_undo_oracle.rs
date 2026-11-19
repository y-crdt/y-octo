//! Replays the scripted UndoManager scenarios of `oracle/undo.mjs` with
//! y-octo's own [UndoManager] and checks every step against what Yjs recorded
//! under both pinned versions (13.6.33 authoritative).

mod support;

use std::collections::VecDeque;

use serde_json::Value as Json;
use support::{concurrent::assert_snapshot, *};
use y_octo::{
    Any, Array, Doc, Map, Origin, Text, TextDeltaOp, TextInsert, TransactionMut, UndoManager, UndoOptions, UndoScope,
    Value,
};

fn corpus() -> Json {
    read_gzip_jsonl(include_bytes!("oracle/undo.jsonl.gz"))
}

fn any(value: &Json) -> Any {
    serde_json::from_value(value.clone()).unwrap()
}

fn attrs(value: &Json) -> Option<y_octo::TextAttributes> {
    value
        .as_object()
        .map(|attrs| attrs.iter().map(|(k, v)| (k.clone(), any(v))).collect())
}

/// A document with handles of its three roots, taken outside transactions.
struct Replica {
    doc: Doc,
    text: Text,
    array: Array,
    map: Map,
}

impl Replica {
    fn new(client: u64) -> Self {
        let doc = support::doc(client, true);
        Self {
            text: doc.get_or_create_text("text").unwrap(),
            array: doc.get_or_create_array("array").unwrap(),
            map: doc.get_or_create_map("map").unwrap(),
            doc,
        }
    }
}

/// The new nested types a step inserts, created before its transaction (a
/// type is created outside the transaction that mounts it).
fn new_types(doc: &Doc, step: &Json) -> VecDeque<Value> {
    let mut types = VecDeque::new();
    for edit in step["edits"].as_array().unwrap() {
        let values = match edit.get("values") {
            Some(values) => values.as_array().unwrap().iter().collect::<Vec<_>>(),
            None => edit.get("value").into_iter().collect(),
        };
        for value in values {
            match value.get("new").and_then(Json::as_str) {
                Some("text") => types.push_back(Value::Text(doc.create_text().unwrap())),
                Some("array") => types.push_back(Value::Array(doc.create_array().unwrap())),
                Some("map") => types.push_back(Value::Map(doc.create_map().unwrap())),
                _ => {}
            }
        }
    }
    types
}

/// The value to insert: the next new nested type or a plain value.
fn value(types: &mut VecDeque<Value>, value: &Json) -> Value {
    match value.get("new") {
        Some(_) => types.pop_front().unwrap(),
        None => Value::Any(any(value)),
    }
}

/// Resolves a root name followed by map keys or array indices inside `tx`.
fn target(replica: &Replica, tx: &mut TransactionMut<'_>, path: &Json) -> Value {
    let path = path.as_array().unwrap();
    let mut current = match path[0].as_str().unwrap() {
        "text" => Value::Text(replica.text.clone()),
        "array" => Value::Array(replica.array.clone()),
        _ => Value::Map(replica.map.clone()),
    };
    for step in &path[1..] {
        current = match (&current, step) {
            (Value::Map(map), Json::String(key)) => tx.map(map).unwrap().get(key).unwrap(),
            (Value::Array(array), Json::Number(index)) => {
                tx.array(array).unwrap().get(index.as_u64().unwrap()).unwrap()
            }
            (value, step) => panic!("cannot step into {value:?} with {step}"),
        };
    }
    current
}

fn text_ops(index: u64, op: TextDeltaOp) -> Vec<TextDeltaOp> {
    let mut ops = Vec::new();
    if index > 0 {
        ops.push(TextDeltaOp::Retain {
            retain: index,
            format: None,
        });
    }
    ops.push(op);
    ops
}

fn edit(replica: &Replica, tx: &mut TransactionMut<'_>, types: &mut VecDeque<Value>, edit: &Json) {
    let index = edit["index"].as_u64().unwrap_or(0);
    match (edit["kind"].as_str().unwrap(), target(replica, tx, &edit["target"])) {
        ("insert", Value::Text(text)) => tx
            .text(&text)
            .unwrap()
            .apply_delta(&text_ops(
                index,
                TextDeltaOp::Insert {
                    insert: TextInsert::Text(edit["text"].as_str().unwrap().into()),
                    format: attrs(&edit["attrs"]),
                },
            ))
            .unwrap(),
        ("insert", Value::Array(array)) => {
            let mut array = tx.array(&array).unwrap();
            for (offset, v) in edit["values"].as_array().unwrap().iter().enumerate() {
                array.insert(index + offset as u64, value(types, v)).unwrap();
            }
        }
        ("delete", Value::Text(text)) => tx
            .text(&text)
            .unwrap()
            .remove(index, edit["len"].as_u64().unwrap())
            .unwrap(),
        ("delete", Value::Array(array)) => tx
            .array(&array)
            .unwrap()
            .remove(index, edit["len"].as_u64().unwrap())
            .unwrap(),
        ("format", Value::Text(text)) => tx
            .text(&text)
            .unwrap()
            .apply_delta(&text_ops(
                index,
                TextDeltaOp::Retain {
                    retain: edit["len"].as_u64().unwrap(),
                    format: attrs(&edit["attrs"]),
                },
            ))
            .unwrap(),
        ("set", Value::Map(map)) => tx
            .map(&map)
            .unwrap()
            .insert(edit["key"].as_str().unwrap().into(), value(types, &edit["value"]))
            .unwrap(),
        ("remove", Value::Map(map)) => tx.map(&map).unwrap().remove(edit["key"].as_str().unwrap()),
        (kind, target) => panic!("cannot {kind} {target:?}"),
    }
}

fn scope(replica: &Replica, scope: &Json) -> Vec<UndoScope> {
    match scope {
        Json::String(s) if s == "doc" => vec![(&replica.doc).into()],
        Json::Array(roots) => roots
            .iter()
            .map(|root| match root.as_str().unwrap() {
                "text" => UndoScope::from(&replica.text),
                "array" => UndoScope::from(&replica.array),
                _ => UndoScope::from(&replica.map),
            })
            .collect(),
        _ => unreachable!(),
    }
}

fn replay(scenario: &Json) {
    let name = scenario["name"].as_str().unwrap();
    let versions = &scenario["versions"];
    let a = Replica::new(101);
    let b = Replica::new(202);
    let replicas = |name: &Json| if name == "a" { &a } else { &b };
    let undo = UndoManager::<()>::new(
        &a.doc,
        scope(&a, &scenario["scope"]),
        UndoOptions {
            // like the generator's MAX_SAFE_INTEGER timeout: only stops split
            capture_timeout: u64::MAX,
            ..Default::default()
        },
    )
    .unwrap();
    undo.advance_time(1);

    for (i, (step, expected)) in scenario["steps"]
        .as_array()
        .unwrap()
        .iter()
        .zip(scenario["expected"].as_array().unwrap())
        .enumerate()
    {
        let context = format!("{name} {versions} step {i} {step}");
        let mut performed = None;
        match step["op"].as_str().unwrap() {
            "tx" => {
                let replica = replicas(&step["doc"]);
                let origin = step["origin"].as_str().map(|origin| Origin::new(origin.to_string()));
                let mut types = new_types(&replica.doc, step);
                replica
                    .doc
                    .transact_mut(origin, |tx| {
                        for e in step["edits"].as_array().unwrap() {
                            edit(replica, tx, &mut types, e);
                        }
                        Ok(())
                    })
                    .unwrap();
            }
            "sync" => {
                let (from, to) = (&replicas(&step["from"]).doc, &replicas(&step["to"]).doc);
                let update = from.encode_state_as_update(&to.get_state_vector()).unwrap();
                to.apply_update_with_origin(update, Origin::new("remote")).unwrap();
            }
            "undo" => performed = Some(undo.undo().unwrap().is_some()),
            "redo" => performed = Some(undo.redo().unwrap().is_some()),
            "stop" => undo.stop_capturing().unwrap(),
            "clear" => undo.clear(true, true).unwrap(),
            op => panic!("unknown step {op}"),
        }
        assert_eq!(performed, expected["performed"].as_bool(), "{context}: performed");
        assert_eq!(undo.can_undo(), expected["can_undo"], "{context}: can_undo");
        assert_eq!(undo.can_redo(), expected["can_redo"], "{context}: can_redo");
        assert_snapshot(&a.doc, &expected["a"], &format!("{context}: a"));
        assert_snapshot(&b.doc, &expected["b"], &format!("{context}: b"));
    }
}

#[test]
#[cfg_attr(miri, ignore = "Large semantic oracle; ordinary tests cover it")]
fn yjs_undo_scenarios_match_every_step() {
    let corpus = corpus();
    assert_provenance(&corpus);
    for scenario in corpus["records"].as_array().unwrap() {
        // Where the versions differ, the port follows 13.6.33: #757 (no
        // cross-parent left for a recreated map value) and document scopes,
        // which 13.6.21 does not have.
        if !scenario["versions"]
            .as_array()
            .unwrap()
            .contains(&serde_json::json!("13.6.33"))
        {
            assert!(
                corpus["version_differences"]
                    .as_array()
                    .unwrap()
                    .contains(&scenario["name"])
            );
            continue;
        }
        replay(scenario);
    }
}
