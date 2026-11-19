mod support;
use std::{
    io::{BufRead, BufReader, Write},
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
    sync::{Arc, Mutex},
};

use serde_json::{Value as Json, json};
use y_octo::{CommitEvent, Doc, Origin, StateVector, Subscription, TextDeltaOp, Update};
fn state(sv: &StateVector) -> Vec<(u64, u64)> {
    let mut out: Vec<_> = sv.iter().map(|(c, k)| (*c, *k)).collect();
    out.sort();
    out
}
fn deleted(mut update: Update) -> Json {
    let ceiling = StateVector::from([(101, u64::MAX), (202, u64::MAX), (303, u64::MAX), (404, u64::MAX)]);
    let mut grouped = std::collections::BTreeMap::<u64, Vec<(u64, u64)>>::new();
    for (client, r) in update.delete_set_iter(ceiling) {
        grouped.entry(client).or_default().push((r.start, r.end - r.start));
    }
    json!(grouped.into_iter().collect::<Vec<_>>())
}
fn event(e: &CommitEvent) -> Json {
    let mut inserted: Vec<_> = e
        .after_state
        .iter()
        .filter_map(|(c, end)| {
            let start = e.before_state.get(c);
            (*end > start).then(|| (*c, vec![(start, end - start)]))
        })
        .collect();
    inserted.sort();
    let mut changed: Vec<_> = e
        .changed
        .iter()
        .filter_map(|t| match &t.identity {
            y_octo::TypeIdentity::Root(s) => Some(s.clone()),
            _ => None,
        })
        .collect();
    changed.sort();
    json!({"local":e.local,"before":state(&e.before_state),"after":state(&e.after_state),"inserted":inserted,"deleted":deleted(Update::decode_v1(&e.update).unwrap()),"changed":changed})
}
struct Bridge {
    child: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
}
impl Bridge {
    fn new(version: &str, gc: bool) -> Self {
        let mut child = Command::new("node")
            .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/oracle/format-cleanup.mjs"))
            .arg(version)
            .arg(gc.to_string())
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        Self {
            input: child.stdin.take().unwrap(),
            output: BufReader::new(child.stdout.take().unwrap()),
            child,
        }
    }
    fn request(&mut self, v: Json) -> Json {
        writeln!(self.input, "{}", v).unwrap();
        self.input.flush().unwrap();
        let mut line = String::new();
        self.output.read_line(&mut line).unwrap();
        assert!(!line.is_empty(), "oracle exited");
        serde_json::from_str(&line).unwrap()
    }
}
impl Drop for Bridge {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}
fn delta(op: &Json) -> Vec<TextDeltaOp> {
    op["value"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| {
            let mut v = v.clone();
            let o = v.as_object_mut().unwrap();
            if let Some(attrs) = o.remove("attributes") {
                o.insert("format".into(), attrs);
            }
            if let Some(insert) = o.get_mut("insert")
                && !insert.is_string()
            {
                *insert = json!([insert.clone()]);
            }
            serde_json::from_value(v).unwrap()
        })
        .collect()
}
fn apply(docs: &[Doc; 2], op: &Json) {
    let actor = op["actor"].as_u64().unwrap_or(0) as usize;
    let mut text = docs[actor].get_or_create_text("text").unwrap();
    match op["kind"].as_str().unwrap() {
        "delta" => text.apply_delta(&delta(op)).unwrap(),
        "remove" => text
            .remove(op["index"].as_u64().unwrap(), op["length"].as_u64().unwrap())
            .unwrap(),
        "sync" => {
            let from = op["from"].as_u64().unwrap() as usize;
            let to = op["to"].as_u64().unwrap() as usize;
            let update = docs[from]
                .encode_state_as_update_v1(&docs[to].get_state_vector())
                .unwrap();
            docs[to]
                .apply_update_with_origin(Update::decode_v1(&update).unwrap(), Origin::new("wire"))
                .unwrap();
            if op["repeat"] == true {
                docs[to]
                    .apply_update_with_origin(Update::decode_v1(&update).unwrap(), Origin::new("wire"))
                    .unwrap();
            }
        }
        other => panic!("{other}"),
    }
}
fn record(doc: &Doc) -> (Subscription, Arc<Mutex<Vec<CommitEvent>>>) {
    let events = Arc::new(Mutex::new(Vec::new()));
    let sink = events.clone();
    let sub = doc.subscribe(move |e| sink.lock().unwrap().push(e.clone()));
    (sub, events)
}

#[test]
#[ignore = "Requires Node and npm ci --prefix y-octo/tests/oracle"]
fn online_format_cleanup_persistent_replicas() {
    for version in ["13.6.21", "13.6.33"] {
        for gc in [false, true] {
            let mut bridge = Bridge::new(version, gc);
            for (name, ops) in scenarios() {
                let docs = [support::doc(101, gc), support::doc(202, gc)];
                let mut mirrors = [support::doc(303, gc), support::doc(404, gc)];
                for d in docs.iter().chain(&mirrors) {
                    d.get_or_create_text("text").unwrap();
                    d.get_or_create_array("array").unwrap();
                    d.get_or_create_map("map").unwrap();
                }
                let recording = docs.each_ref().map(record);
                bridge.request(json!({"op":{"kind":"reset"},"rust_updates":[[],[]]}));
                for (step, op) in ops.iter().enumerate() {
                    let before: Vec<_> = docs
                        .iter()
                        .map(|d| support::trace::encode_hex(&d.encode_update_v1().unwrap()))
                        .collect();
                    apply(&docs, op);
                    let events = recording
                        .each_ref()
                        .map(|(_, r)| std::mem::take(&mut *r.lock().unwrap()));
                    let updates = events.each_ref().map(|e| {
                        e.iter()
                            .map(|e| support::trace::encode_hex(&e.update))
                            .collect::<Vec<_>>()
                    });
                    let reply = bridge.request(json!({"op":op,"rust_updates":updates}));
                    for actor in 0..2 {
                        let context = format!("{version} gc={gc} {name} step {step} actor {actor} {op}");
                        if support::snapshot(&docs[actor]) != reply["states"][actor] {
                            let _ = support::trace::save_failure(
                                &json!({"version":version,"gc":gc,"name":name,"step":step,"actor":actor,"before":before,"ops":ops[..=step],"next":op,"expected":reply["states"][actor],"actual":support::snapshot(&docs[actor])}),
                                "format-cleanup",
                            );
                        }
                        assert_eq!(
                            support::snapshot(&docs[actor]),
                            reply["states"][actor],
                            "canonical {context}"
                        );
                        assert_eq!(
                            support::snapshot(&docs[actor]),
                            reply["mirrors"][actor],
                            "Rust → persistent Yjs {context}"
                        );
                        let actual: Vec<_> = events[actor].iter().map(event).collect();
                        let mut expected = reply["events"][actor].clone();
                        for e in expected.as_array_mut().unwrap() {
                            mirrors[actor]
                                .apply_update_from_binary_v1(support::bytes(&e["update"]))
                                .unwrap();
                            e.as_object_mut().unwrap().remove("update");
                        }
                        assert_eq!(json!(actual), expected, "commit boundaries {context}");
                        assert_eq!(
                            support::snapshot(&mirrors[actor]),
                            reply["states"][actor],
                            "Yjs → persistent Rust {context}"
                        );
                    }
                }
                eprintln!("{version} gc={gc}: {name} {} operations verified", ops.len());
            }
        }
    }
}
fn scenarios() -> Vec<(&'static str, Vec<Json>)> {
    let insert = |s: &str| json!({"kind":"delta","value":[{"insert":s}]});
    let format = |actor, attrs: Json| json!({"kind":"delta","actor":actor,"value":[{"retain":1,"attributes":attrs}]});
    let sync = |from, to| json!({"kind":"sync","from":from,"to":to,"repeat":true});
    let mut cases = vec![
        (
            "local-empty-gap",
            vec![
                json!({"kind":"delta","value":[{"insert":"abc","attributes":{"bold":true}}]}),
                json!({"kind":"remove","index":0,"length":3}),
                insert("next"),
                sync(0, 1),
                sync(1, 0),
            ],
        ),
        (
            "delete-and-insert-cursor",
            vec![
                json!({"kind":"delta","value":[{"insert":"a","attributes":{"bold":true}},{"insert":"b","attributes":{"italic":true}},{"insert":"c"}]}),
                json!({"kind":"delta","value":[{"retain":1},{"delete":1},{"insert":"X"}]}),
                sync(0, 1),
                sync(1, 0),
            ],
        ),
        (
            "concurrent-duplicate-format",
            vec![
                insert("ab"),
                sync(0, 1),
                format(0, json!({"bold":true})),
                format(1, json!({"bold":true})),
                sync(1, 0),
                sync(0, 1),
                sync(1, 0),
            ],
        ),
        (
            "concurrent-object-format",
            vec![
                insert("ab"),
                sync(0, 1),
                format(0, json!({"link":{"href":"x"}})),
                format(1, json!({"link":{"href":"x"}})),
                sync(1, 0),
                sync(0, 1),
                json!({"kind":"remove","index":0,"length":1}),
                sync(0, 1),
                sync(1, 0),
            ],
        ),
        (
            "format-delete-conflict",
            vec![
                insert("abcd"),
                sync(0, 1),
                format(0, json!({"bold":true})),
                json!({"kind":"remove","actor":1,"index":0,"length":2}),
                sync(1, 0),
                sync(0, 1),
                sync(1, 0),
            ],
        ),
    ];
    for (name, attribute) in [
        ("flat-equal-format-tail", json!({"href":"x"})),
        ("distinct-nested-format-tail", json!({"link":{"href":"x"}})),
    ] {
        // The two commands create separate attribute values on each replica.
        cases.push((
            name,
            vec![
                json!({"kind":"delta","value":[{"insert":"a"},{"insert":"b","attributes":{"style":attribute}}]}),
                format(0, json!({"style":attribute})),
                sync(0, 1),
                sync(1, 0),
            ],
        ));
    }
    cases.push((
        "delete-after-first-local-and-remote-format",
        vec![
            insert("abc"),
            sync(0, 1),
            json!({"kind":"remove","index":2,"length":1}),
            sync(0, 1),
            format(0, json!({"bold":true})),
            sync(0, 1),
            json!({"kind":"remove","actor":1,"index":0,"length":1}),
            sync(1, 0),
            json!({"kind":"remove","index":0,"length":1}),
            sync(0, 1),
        ],
    ));
    cases.push((
        "mixed-old-and-new-tombstones",
        vec![
            insert("abcd"),
            sync(0, 1),
            json!({"kind":"delta","value":[{"insert":"X","attributes":{"bold":true}}]}),
            json!({"kind":"remove","index":0,"length":1}),
            json!({"kind":"remove","index":1,"length":1}),
            json!({"kind":"delta","value":[{"retain":3},{"insert":"!"}]}),
            sync(0, 1),
            sync(1, 0),
        ],
    ));
    cases.push((
        "utf16-formatted-gap",
        vec![
            json!({"kind":"delta","value":[{"insert":"A😀Z","attributes":{"bold":true}}]}),
            json!({"kind":"remove","index":1,"length":2}),
            json!({"kind":"delta","value":[{"retain":1},{"delete":1},{"insert":"!"}]}),
            sync(0, 1),
            sync(1, 0),
        ],
    ));
    let model = [support::doc(101, true), support::doc(202, true)];
    let mut schedule = vec![insert("abcdefgh"), sync(0, 1)];
    for op in &schedule {
        apply(&model, op);
    }
    for round in 0..24 {
        let actor = round % 2;
        let op = format(
            actor,
            json!({"bold":round%3==0,"link":{"href":format!("ref{}",round%4)}}),
        );
        apply(&model, &op);
        schedule.push(op);
        let op = if model[actor as usize].get_or_create_text("text").unwrap().len() > 3 && round % 3 == 0 {
            json!({"kind":"remove","actor":actor,"index":1,"length":1})
        } else {
            json!({"kind":"delta","actor":actor,"value":[{"insert":"x"}]})
        };
        apply(&model, &op);
        schedule.push(op);
        if round % 3 == 2 {
            for op in [sync(1, 0), sync(0, 1)] {
                apply(&model, &op);
                schedule.push(op);
            }
        }
    }
    schedule.extend([sync(0, 1), sync(1, 0), sync(0, 1)]);
    cases.push(("seeded-format-schedule", schedule));
    cases
}
