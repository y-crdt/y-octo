//! Differential test of the Lean YATA model (`proofs-yata`) against y-octo.
//!
//! Replicas edit one text concurrently and exchange their updates in any
//! order, some of them twice and some as state diffs that start inside a
//! struct, so that integration has to split, wait for missing dependencies
//! and skip what it already has. Every update a y-octo replica applies is
//! decoded from its wire bytes and replayed on the same replica of the Lean
//! model; after every step both sides must agree on the visible text, the
//! ids of the visible clocks, the state vector, the delete set, whether
//! structs are pending, and on the origins and content of every clock. After
//! `Doc::gc` they must also agree on the struct boundaries.
//!
//! The model is the executable `yocto-spec` of `proofs-yata`; the path of the
//! binary is taken from `YOCTO_SPEC_BIN`. Without it only the y-octo side
//! runs: the replicas must converge, and `ReadDoc`, the second integration
//! engine of this crate, must read the same text. With `YOCTO_SPEC_REQUIRE=1`
//! (set in CI) a missing binary fails the tests instead.

use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
    process::Command,
    sync::{Arc, Mutex},
};

use rand::{RngExt, SeedableRng};
use rand_chacha::ChaCha20Rng;
use serde_json::{Value as Json, json};
use y_octo::{Doc, DocOptions, ReadDoc, Subscription, Text, TextInsert};

const ROOT: &str = "t";

// --- Update V1 wire structs of a text ---

type WireId = (u64, u64);

#[derive(Clone, Debug, PartialEq)]
enum Kind {
    /// `ContentString`
    Item(String),
    /// `ContentDeleted`
    Deleted,
    Gc,
    Skip,
}

#[derive(Clone, Debug)]
struct Struct {
    client: u64,
    clock: u64,
    len: u64,
    kind: Kind,
    left: Option<WireId>,
    right: Option<WireId>,
}

struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl Reader<'_> {
    fn byte(&mut self) -> u8 {
        let byte = self.bytes[self.pos];
        self.pos += 1;
        byte
    }

    fn var(&mut self) -> u64 {
        let mut value = 0u64;
        let mut shift = 0;
        loop {
            let byte = self.byte();
            value |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return value;
            }
            shift += 7;
        }
    }

    fn string(&mut self) -> String {
        let len = self.var() as usize;
        let value = std::str::from_utf8(&self.bytes[self.pos..self.pos + len]).unwrap();
        self.pos += len;
        value.to_string()
    }

    fn id(&mut self) -> WireId {
        (self.var(), self.var())
    }
}

/// The structs and the delete set of an update of a document that only holds
/// the text `ROOT`.
fn decode_update(bytes: &[u8]) -> (Vec<Struct>, Vec<(u64, u64, u64)>) {
    let mut reader = Reader { bytes, pos: 0 };
    let mut structs = Vec::new();
    for _ in 0..reader.var() {
        let count = reader.var();
        let client = reader.var();
        let mut clock = reader.var();
        for _ in 0..count {
            let info = reader.byte();
            let (len, kind, left, right) = if info == 10 {
                (reader.var(), Kind::Skip, None, None)
            } else if info & 0x1f == 0 {
                (reader.var(), Kind::Gc, None, None)
            } else {
                let left = (info & 0x80 != 0).then(|| reader.id());
                let right = (info & 0x40 != 0).then(|| reader.id());
                if left.is_none() && right.is_none() {
                    assert_eq!(reader.var(), 1, "the parent is the root type");
                    assert_eq!(reader.string(), ROOT);
                    assert_eq!(info & 0x20, 0, "text items have no parent key");
                }
                match info & 0x1f {
                    1 => (reader.var(), Kind::Deleted, left, right),
                    4 => {
                        let text = reader.string();
                        (text.encode_utf16().count() as u64, Kind::Item(text), left, right)
                    }
                    other => panic!("content {other} is not part of the text model"),
                }
            };
            structs.push(Struct {
                client,
                clock,
                len,
                kind,
                left,
                right,
            });
            clock += len;
        }
    }
    let mut deleted = Vec::new();
    for _ in 0..reader.var() {
        let client = reader.var();
        for _ in 0..reader.var() {
            let clock = reader.var();
            deleted.push((client, clock, reader.var()));
        }
    }
    assert_eq!(reader.pos, bytes.len(), "update not fully decoded");
    (structs, deleted)
}

fn id_json(id: Option<WireId>) -> Json {
    id.map_or(Json::Null, |(client, clock)| json!([client, clock]))
}

/// The `apply` step of the model for an update.
fn apply_step(replica: usize, bytes: &[u8]) -> Json {
    let (structs, deleted) = decode_update(bytes);
    let structs = structs
        .iter()
        .map(|s| {
            let mut value = json!({"client": s.client, "clock": s.clock, "len": s.len});
            let (kind, text) = match &s.kind {
                Kind::Item(text) => ("item", Some(text.clone())),
                Kind::Deleted => ("deleted", None),
                Kind::Gc => ("gc", None),
                Kind::Skip => ("skip", None),
            };
            value["kind"] = json!(kind);
            if let Some(text) = text {
                value["text"] = json!(text);
            }
            if !matches!(s.kind, Kind::Gc | Kind::Skip) {
                value["left"] = id_json(s.left);
                value["right"] = id_json(s.right);
            }
            value
        })
        .collect::<Vec<_>>();
    let deleted = deleted.iter().map(|d| json!([d.0, d.1, d.2])).collect::<Vec<_>>();
    json!({"op": "apply", "replica": replica, "structs": structs, "ds": deleted})
}

// --- y-octo replicas ---

struct Peer {
    doc: Doc,
    text: Text,
    /// the updates of the local commits, in order
    outbox: Arc<Mutex<Vec<Vec<u8>>>>,
    _subscription: Subscription,
}

impl Peer {
    fn new(client: u64, gc: bool) -> Self {
        let doc = DocOptions::from_identity(client, "lean-yata".into())
            .auto_gc(gc)
            .build();
        let text = doc.get_or_create_text(ROOT).unwrap();
        let outbox = Arc::new(Mutex::new(Vec::new()));
        let sink = outbox.clone();
        let subscription = doc.subscribe(move |event| {
            if event.local {
                sink.lock().unwrap().push(event.update.clone());
            }
        });
        Self {
            doc,
            text,
            outbox,
            _subscription: subscription,
        }
    }

    fn sent(&self) -> usize {
        self.outbox.lock().unwrap().len()
    }

    fn update(&self, index: usize) -> Vec<u8> {
        self.outbox.lock().unwrap()[index].clone()
    }

    fn delete_ranges(&self) -> Vec<(u64, u64, u64)> {
        let mut ranges = Vec::new();
        for (client, deleted) in self.doc.get_delete_sets().iter() {
            for range in deleted {
                ranges.push((*client, range.start, range.end - range.start));
            }
        }
        ranges.sort_unstable();
        // adjacent ranges are one range
        let mut merged: Vec<(u64, u64, u64)> = Vec::new();
        for range in ranges {
            match merged.last_mut() {
                Some(last) if last.0 == range.0 && last.1 + last.2 == range.1 => last.2 += range.2,
                _ => merged.push(range),
            }
        }
        merged
    }

    /// The state the model has to be in, in the shape `yocto-spec` prints.
    fn snapshot(&self) -> Json {
        let mut ids = Vec::new();
        for run in self.text.identity_runs().unwrap() {
            let TextInsert::Text(text) = run.insert else {
                panic!("the text only holds strings");
            };
            for offset in 0..text.encode_utf16().count() as u64 {
                ids.push(json!([run.id.client, run.id.clock + offset]));
            }
        }
        let state = self.doc.get_state_vector();
        let mut sv = state
            .iter()
            .map(|(client, clock)| (*client, *clock))
            .collect::<Vec<_>>();
        sv.retain(|(_, clock)| *clock > 0);
        sv.sort_unstable();
        let deleted = self.delete_ranges();
        let pending = self.doc.has_pending_updates();
        let mut snapshot = json!({
            "text": self.text.to_string(),
            "ids": ids,
            "sv": sv.iter().map(|(client, clock)| json!([client, clock])).collect::<Vec<_>>(),
            "ds": deleted.iter().map(|d| json!([d.0, d.1, d.2])).collect::<Vec<_>>(),
            "pending": pending,
        });
        if !pending {
            // with pending structs the encoded state also carries them
            let (structs, _) = decode_update(&self.doc.encode_update_v1().unwrap());
            let is_deleted = |client: u64, clock: u64| {
                deleted
                    .iter()
                    .any(|d| d.0 == client && d.1 <= clock && clock < d.1 + d.2)
            };
            let mut units = BTreeMap::new();
            let mut blocks = BTreeMap::new();
            for s in &structs {
                let content = match &s.kind {
                    Kind::Item(text) => text.encode_utf16().map(|unit| Some(u64::from(unit))).collect(),
                    _ => vec![None; s.len as usize],
                };
                let gc = matches!(s.kind, Kind::Gc);
                for (offset, unit) in content.into_iter().enumerate() {
                    let clock = s.clock + offset as u64;
                    let left = if offset == 0 {
                        s.left
                    } else {
                        Some((s.client, clock - 1))
                    };
                    let (left, right) = if gc { (None, None) } else { (left, s.right) };
                    units.insert(
                        (s.client, clock),
                        json!([
                            s.client,
                            clock,
                            id_json(left),
                            id_json(right),
                            unit,
                            gc,
                            gc || is_deleted(s.client, clock)
                        ]),
                    );
                }
                if !gc {
                    let kind = if matches!(s.kind, Kind::Item(_)) { "str" } else { "del" };
                    blocks.insert(
                        (s.client, s.clock),
                        json!([s.client, s.clock, s.len, kind, is_deleted(s.client, s.clock)]),
                    );
                }
            }
            snapshot["units"] = units.into_values().collect();
            snapshot["blocks"] = blocks.into_values().collect();
        }
        snapshot
    }

    /// `ReadDoc` integrates the encoded state from scratch with its own
    /// index-based store; it has to read the same text.
    fn check_read_doc(&self) {
        if self.doc.has_pending_updates() {
            return;
        }
        let bytes = self.doc.encode_update_v1().unwrap();
        let read = ReadDoc::from_full_update_v1(bytes).unwrap();
        let text = read.text(ROOT).map(|text| text.to_string()).unwrap_or_default();
        assert_eq!(text, self.text.to_string(), "ReadDoc and Doc disagree");
    }
}

// --- Scenarios ---

struct Step {
    /// the step of the model
    op: Json,
    replica: usize,
    /// the state of the y-octo replica after it
    expected: Json,
    /// whether the struct boundaries are canonical (right after `Doc::gc`)
    canonical: bool,
}

struct Scenario {
    name: String,
    peers: Vec<Peer>,
    /// `delivered[to][from]`: which updates of `from` reached `to`
    delivered: Vec<Vec<Vec<bool>>>,
    steps: Vec<Step>,
}

impl Scenario {
    fn new(name: impl Into<String>, replicas: &[(u64, bool)]) -> Self {
        let count = replicas.len();
        Self {
            name: name.into(),
            peers: replicas.iter().map(|&(client, gc)| Peer::new(client, gc)).collect(),
            delivered: vec![vec![Vec::new(); count]; count],
            steps: Vec::new(),
        }
    }

    fn record(&mut self, replica: usize, op: Json, canonical: bool) {
        let expected = self.peers[replica].snapshot();
        self.peers[replica].check_read_doc();
        self.steps.push(Step {
            op,
            replica,
            expected,
            canonical,
        });
    }

    /// A local edit: the model replays the update of its commit.
    fn local(&mut self, replica: usize, edit: impl FnOnce(&mut Text)) {
        let before = self.peers[replica].sent();
        edit(&mut self.peers[replica].text);
        let after = self.peers[replica].sent();
        for index in before..after {
            let bytes = self.peers[replica].update(index);
            self.record(replica, apply_step(replica, &bytes), false);
        }
    }

    fn insert(&mut self, replica: usize, index: u64, text: &str) {
        self.local(replica, |t| t.insert(index, text).unwrap());
    }

    fn remove(&mut self, replica: usize, index: u64, len: u64) {
        self.local(replica, |t| t.remove(index, len).unwrap());
    }

    fn apply(&mut self, to: usize, bytes: &[u8]) {
        self.peers[to].doc.apply_update_from_binary_v1(bytes).unwrap();
        self.record(to, apply_step(to, bytes), false);
    }

    /// Delivers the update `index` of `from` to `to`, whatever was delivered
    /// before.
    fn deliver(&mut self, from: usize, to: usize, index: usize) {
        let bytes = self.peers[from].update(index);
        let delivered = &mut self.delivered[to][from];
        if delivered.len() <= index {
            delivered.resize(index + 1, false);
        }
        delivered[index] = true;
        self.apply(to, &bytes);
    }

    /// Sends `to` what its state vector lacks of the state of `from`.
    fn sync(&mut self, from: usize, to: usize) {
        let state = self.peers[to].doc.get_state_vector();
        let bytes = self.peers[from].doc.encode_state_as_update_v1(&state).unwrap();
        self.apply(to, &bytes);
    }

    /// Like `sync`, but the model computes the state diff itself (its `sync`
    /// step, pending structs and deletions included) instead of replaying the
    /// bytes y-octo encoded.
    fn sync_by_model(&mut self, from: usize, to: usize) {
        let state = self.peers[to].doc.get_state_vector();
        let bytes = self.peers[from].doc.encode_state_as_update_v1(&state).unwrap();
        self.peers[to].doc.apply_update_from_binary_v1(&bytes).unwrap();
        self.record(to, json!({"op": "sync", "from": from, "to": to}), false);
    }

    fn gc(&mut self, replica: usize) {
        self.peers[replica].doc.gc().unwrap();
        self.record(replica, json!({"op": "gc", "replica": replica}), true);
    }

    fn undelivered(&self, from: usize, to: usize) -> Vec<usize> {
        let delivered = &self.delivered[to][from];
        (0..self.peers[from].sent())
            .filter(|&index| !delivered.get(index).copied().unwrap_or(false))
            .collect()
    }

    /// Delivers everything that is still on its way, in order, then lets every
    /// replica collect; all replicas must then be in the same state.
    fn settle(&mut self) {
        let count = self.peers.len();
        for to in 0..count {
            for from in 0..count {
                if from != to {
                    for index in self.undelivered(from, to) {
                        self.deliver(from, to, index);
                    }
                }
            }
        }
        // state diffs carry what a replica only received from a third one
        for to in 0..count {
            for from in 0..count {
                if from != to {
                    self.sync(from, to);
                }
            }
        }
        for replica in 0..count {
            self.gc(replica);
        }
        let first = self.peers[0].snapshot();
        for (replica, peer) in self.peers.iter().enumerate() {
            let snapshot = peer.snapshot();
            assert!(
                !peer.doc.has_pending_updates(),
                "{}: replica {replica} still waits",
                self.name
            );
            for key in ["text", "ids", "sv", "ds", "units", "blocks"] {
                assert_eq!(
                    snapshot[key], first[key],
                    "{}: replicas 0 and {replica} did not converge on {key}",
                    self.name
                );
            }
        }
    }

    fn trace(&self) -> Json {
        json!({
            "replicas": self
                .peers
                .iter()
                .map(|peer| json!({"client": peer.doc.client(), "gc": peer.doc.options().gc}))
                .collect::<Vec<_>>(),
            "steps": self.steps.iter().map(|step| step.op.clone()).collect::<Vec<_>>(),
        })
    }
}

/// Random concurrent edits, deliveries in any order, duplicates, state diffs
/// and collections.
fn random_scenario(seed: u64, replicas: &[(u64, bool)], rounds: usize) -> Scenario {
    random_scenario_with(seed, replicas, rounds, false)
}

/// With `model_sync`, half of the state diffs are the `sync` step of the
/// model, which computes the diff itself, instead of the replayed bytes of
/// y-octo; a replica may also sync from the same sender twice in a row.
fn random_scenario_with(seed: u64, replicas: &[(u64, bool)], rounds: usize, model_sync: bool) -> Scenario {
    const ALPHABET: [&str; 12] = ["a", "b", "c", "d", "e", "x", "y", "z", "é", "ß", "中", "文"];
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let mut scenario = Scenario::new(format!("seed {seed:#x}"), replicas);
    let count = replicas.len();
    for _ in 0..rounds {
        let replica = rng.random_range(0..count);
        let len = scenario.peers[replica].text.len();
        match rng.random_range(0..100) {
            0..40 => {
                let index = rng.random_range(0..=len);
                let text = (0..rng.random_range(1..=4))
                    .map(|_| ALPHABET[rng.random_range(0..ALPHABET.len())])
                    .collect::<String>();
                scenario.insert(replica, index, &text);
            }
            40..55 if len > 0 => {
                let index = rng.random_range(0..len);
                let span = rng.random_range(1..=(len - index).min(3));
                scenario.remove(replica, index, span);
            }
            55..85 => {
                let from = (replica + rng.random_range(1..count)) % count;
                let waiting = scenario.undelivered(from, replica);
                let sent = scenario.peers[from].sent();
                if !waiting.is_empty() {
                    // mostly in order, sometimes any later update first
                    let pick = if rng.random_range(0..3) == 0 {
                        rng.random_range(0..waiting.len())
                    } else {
                        0
                    };
                    scenario.deliver(from, replica, waiting[pick]);
                } else if sent > 0 {
                    // a duplicate
                    scenario.deliver(from, replica, rng.random_range(0..sent));
                }
            }
            85..95 => {
                let from = (replica + rng.random_range(1..count)) % count;
                if model_sync && rng.random_range(0..2) == 0 {
                    scenario.sync_by_model(from, replica);
                    if rng.random_range(0..3) == 0 {
                        scenario.sync_by_model(from, replica);
                    }
                } else {
                    scenario.sync(from, replica);
                }
            }
            95..100 => scenario.gc(replica),
            _ => {}
        }
    }
    scenario.settle();
    scenario
}

/// Hand-written conflicts: the branches of `find_conflict_left`.
fn conflict_scenario() -> Scenario {
    // client ids chosen so that the document order differs from the creation
    // order
    let mut s = Scenario::new("conflicts", &[(5, false), (2, true), (9, false), (7, true)]);
    s.insert(0, 0, "abcdef");
    for to in 1..4 {
        s.deliver(0, to, 0);
    }
    // same origins on three replicas: ordered by client id
    s.insert(1, 3, "11");
    s.insert(2, 3, "22");
    s.insert(3, 3, "33");
    // a later insert of replica 2 between its own text and "d": same left
    // origin for no one, a right origin inside the conflict range for others
    s.insert(2, 5, "!");
    // replica 0 inserts at the same gap after it saw replica 3 only
    s.deliver(3, 0, 0);
    s.insert(0, 3, "00");
    s.insert(0, 4, "+");
    // deletions that split structs, and an insert inside a deleted range
    s.remove(1, 1, 3);
    s.insert(3, 2, "mid");
    s.remove(3, 0, 2);
    // out of order: the second update of a replica before its first
    s.deliver(2, 1, 1);
    s.deliver(2, 1, 0);
    s.deliver(0, 1, 2);
    s.deliver(0, 1, 1);
    s.deliver(0, 2, 1);
    s.gc(1);
    // a state diff that starts inside a struct of the sender
    s.insert(0, 0, "head");
    s.sync(0, 3);
    s.insert(0, 2, "X");
    s.sync(0, 3);
    s.deliver(1, 3, 1);
    s.deliver(1, 3, 1);
    s.settle();
    s
}

// --- The model ---

/// The oracle binary. With `YOCTO_SPEC_REQUIRE=1` a missing binary fails the
/// test instead of leaving the model out.
fn spec_bin() -> Option<PathBuf> {
    let required = std::env::var_os("YOCTO_SPEC_REQUIRE").is_some_and(|value| value == "1");
    let Some(path) = std::env::var_os("YOCTO_SPEC_BIN").map(PathBuf::from) else {
        assert!(!required, "YOCTO_SPEC_REQUIRE=1 but YOCTO_SPEC_BIN is not set");
        return None;
    };
    assert!(
        is_executable(&path),
        "YOCTO_SPEC_BIN does not name an executable file: {}",
        path.display()
    );
    Some(path)
}

fn is_executable(path: &Path) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        path.metadata()
            .is_ok_and(|meta| meta.is_file() && meta.permissions().mode() & 0o111 != 0)
    }
    #[cfg(not(unix))]
    {
        path.is_file()
    }
}

/// Runs a trace on the model.
fn run_model(bin: &Path, name: &str, trace: &Json) -> Json {
    let path = std::env::temp_dir().join(format!(
        "yocto-spec-{}-{}.json",
        std::process::id(),
        name.replace(|c: char| !c.is_ascii_alphanumeric(), "-")
    ));
    std::fs::write(&path, serde_json::to_vec(trace).unwrap()).unwrap();
    let output = Command::new(bin).arg(&path).output().unwrap();
    std::fs::remove_file(&path).ok();
    assert!(
        output.status.success(),
        "{name}: yocto-spec failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

/// Runs the trace of the scenario on the model and compares every step.
fn check_against_model(bin: &Path, scenario: &Scenario) {
    let model = run_model(bin, &scenario.name, &scenario.trace());
    let steps = model["steps"].as_array().unwrap();
    assert_eq!(steps.len(), scenario.steps.len(), "{}: step count", scenario.name);
    for (index, (step, actual)) in scenario.steps.iter().zip(steps).enumerate() {
        assert_eq!(actual["replica"], json!(step.replica), "{} step {index}", scenario.name);
        let mut keys = vec!["text", "ids", "sv", "ds", "pending"];
        if !step.expected["units"].is_null() {
            keys.push("units");
            if step.canonical {
                keys.push("blocks");
            }
        }
        for key in keys {
            let (model, expected) = (comparable(key, &actual[key]), comparable(key, &step.expected[key]));
            assert!(
                model == expected,
                "{} step {index} ({}), replica {}: the model and y-octo disagree on {key}: {}",
                scenario.name,
                step.op["op"],
                step.replica,
                difference(&model, &expected)
            );
        }
    }
    // every replica of the model ends in the state of its y-octo replica
    for (replica, peer) in scenario.peers.iter().enumerate() {
        let expected = peer.snapshot();
        for key in ["text", "ids", "sv", "ds", "pending", "units", "blocks"] {
            let (model, expected) = (
                comparable(key, &model["final"][replica][key]),
                comparable(key, &expected[key]),
            );
            assert!(
                model == expected,
                "{}: final state of replica {replica}: {key}: {}",
                scenario.name,
                difference(&model, &expected)
            );
        }
    }
}

/// The part of a snapshot entry both sides have to agree on. Whether a
/// replica still holds the text of a deleted clock is left out: when the same
/// struct arrives both as a string and as `ContentDeleted` (from a replica
/// that collected it), `Update::merge` keeps the copy of the update whose run
/// reaches the clock first, which is not part of the model. `Doc::gc` drops
/// the text of every deleted clock on both sides.
fn comparable(key: &str, value: &Json) -> Json {
    let mut value = value.clone();
    if key == "units" {
        for unit in value.as_array_mut().into_iter().flatten() {
            if unit[6] == json!(true) {
                unit[4] = Json::Null;
            }
        }
    }
    value
}

/// Where two values differ, for the failure message.
fn difference(model: &Json, expected: &Json) -> String {
    match (model.as_array(), expected.as_array()) {
        (Some(model), Some(expected)) => {
            let index = model
                .iter()
                .zip(expected)
                .position(|(a, b)| a != b)
                .unwrap_or(model.len().min(expected.len()));
            format!(
                "entry {index} of {}/{}: model {} / y-octo {}",
                model.len(),
                expected.len(),
                model.get(index).unwrap_or(&Json::Null),
                expected.get(index).unwrap_or(&Json::Null)
            )
        }
        _ => format!("model {model} / y-octo {expected}"),
    }
}

fn check(scenario: Scenario) -> usize {
    match spec_bin() {
        Some(bin) => {
            check_against_model(&bin, &scenario);
            eprintln!(
                "{}: {} steps agree with the Lean model",
                scenario.name,
                scenario.steps.len()
            );
        }
        None => eprintln!(
            "YOCTO_SPEC_BIN is not set: {} ran on y-octo only ({} steps)",
            scenario.name,
            scenario.steps.len()
        ),
    }
    scenario.steps.len()
}

#[test]
#[cfg_attr(miri, ignore = "Differential scenarios run in ordinary tests")]
fn conflict_branches_match_the_lean_model() {
    assert!(check(conflict_scenario()) > 40);
}

#[test]
#[cfg_attr(miri, ignore = "Differential scenarios run in ordinary tests")]
fn random_two_replicas_match_the_lean_model() {
    for seed in 0..24 {
        check(random_scenario(0x1A7A_0000 + seed, &[(1, false), (2, false)], 120));
    }
}

#[test]
#[cfg_attr(miri, ignore = "Differential scenarios run in ordinary tests")]
fn random_replicas_with_gc_match_the_lean_model() {
    for seed in 0..24 {
        check(random_scenario(
            0x1A7A_1000 + seed,
            &[(40, true), (7, false), (23, true), (11, false)],
            200,
        ));
    }
}

#[test]
#[cfg_attr(miri, ignore = "Differential scenarios run in ordinary tests")]
fn random_many_small_inserts_match_the_lean_model() {
    // every replica types into the same few positions: long conflict scans
    for seed in 0..12 {
        let mut rng = ChaCha20Rng::seed_from_u64(0x1A7A_2000 + seed);
        let mut s = Scenario::new(
            format!("typing {seed}"),
            &[(3, false), (1, true), (4, false), (2, false), (8, true)],
        );
        s.insert(0, 0, "base");
        for to in 1..5 {
            s.deliver(0, to, 0);
        }
        for _ in 0..60 {
            let replica = rng.random_range(0..5);
            let len = s.peers[replica].text.len();
            let index = rng.random_range(0..=len.min(4));
            s.insert(replica, index, ["p", "qq", "rrr"][rng.random_range(0..3)]);
            if rng.random_range(0..4) == 0 {
                let from = (replica + rng.random_range(1..5)) % 5;
                let waiting = s.undelivered(from, replica);
                if let Some(&index) = waiting.get(rng.random_range(0..waiting.len().max(1))) {
                    s.deliver(from, replica, index);
                }
            }
        }
        s.settle();
        check(s);
    }
}

/// `UpdateIterator` consumes a `Skip` whatever its clock is: it must not stay
/// behind as a pending struct.
#[test]
#[cfg_attr(miri, ignore = "Differential scenarios run in ordinary tests")]
fn skip_struct_is_consumed_like_in_the_lean_model() {
    let mut s = Scenario::new("skip", &[(1, false), (2, true)]);
    for replica in 0..2 {
        // one client (5) with one struct: a Skip of 3 clocks from clock 1;
        // empty delete set
        s.apply(replica, &[1, 1, 5, 1, 10, 3, 0]);
        let snapshot = s.peers[replica].snapshot();
        assert_eq!(snapshot["pending"], json!(false));
        assert_eq!(snapshot["sv"], json!([]));
    }
    s.insert(0, 0, "after");
    s.settle();
    check(s);
}

/// The model computes state diffs itself: they carry what the sender still
/// has pending, and start inside a struct when the recipient holds a prefix.
#[test]
#[cfg_attr(miri, ignore = "Differential scenarios run in ordinary tests")]
fn model_sync_carries_pending_structs_and_deletions() {
    let mut s = Scenario::new("model sync", &[(1, false), (2, false), (3, true), (4, false)]);
    s.insert(0, 0, "ab");
    s.insert(0, 2, "cd");
    s.remove(0, 0, 1);
    // replica 1 gets the later edit and the deletion first: both wait
    s.deliver(0, 1, 1);
    s.deliver(0, 1, 2);
    assert!(s.peers[1].doc.has_pending_updates());
    // it syncs to the empty replica 2, which then waits for the same clocks
    s.sync_by_model(1, 2);
    assert!(s.peers[2].doc.has_pending_updates());
    assert_eq!(s.peers[2].text.to_string(), "");
    // the predecessor arrives: everything integrates
    s.deliver(0, 2, 0);
    assert!(!s.peers[2].doc.has_pending_updates());
    assert_eq!(s.peers[2].text.to_string(), "bcd");
    // replica 3 holds a prefix of a struct the sender has merged
    s.deliver(0, 3, 0);
    s.gc(0);
    s.sync_by_model(0, 3);
    assert_eq!(s.peers[3].text.to_string(), "bcd");
    s.deliver(0, 1, 0);
    s.sync_by_model(2, 1);
    s.sync_by_model(1, 0);
    s.settle();
    check(s);
}

/// The state diffs of the model in random runs: replicas that wait for
/// structs sync with each other while they edit, collect and receive updates
/// in any order.
#[test]
#[cfg_attr(miri, ignore = "Differential scenarios run in ordinary tests")]
fn random_model_syncs_match_the_lean_model() {
    for seed in 0..24 {
        check(random_scenario_with(
            0x1A7A_3000 + seed,
            &[(40, true), (7, false), (23, true), (11, false)],
            200,
            true,
        ));
    }
    for seed in 0..12 {
        check(random_scenario_with(
            0x1A7A_4000 + seed,
            &[(1, false), (2, false), (3, false)],
            160,
            true,
        ));
    }
}

/// A replica that waits for structs receives them again, from the same and
/// from another replica: it keeps one copy of what it waits for, and when the
/// missing struct arrives every clock is integrated once. The Lean model is
/// asked directly, at every step before the missing struct arrives, what it
/// would send on: every clock that waits once, not once per time it came.
#[test]
#[cfg_attr(miri, ignore = "Differential scenarios run in ordinary tests")]
fn repeated_sync_does_not_duplicate_pending_structs() {
    let mut s = Scenario::new("pending twice", &[(1, false), (2, false), (3, true)]);
    s.insert(0, 0, "ab");
    s.insert(0, 2, "cd");
    s.insert(0, 1, "x");
    s.remove(0, 0, 2);
    // replica 1 misses the first update: the rest waits
    for index in 1..4 {
        s.deliver(0, 1, index);
    }
    assert!(s.peers[1].doc.has_pending_updates());
    // the clocks and the deleted clocks of the encoded state, which carries
    // what waits: every clock once, however the structs are cut
    let waiting = |peer: &Peer| {
        let (structs, deleted) = decode_update(&peer.doc.encode_update_v1().unwrap());
        let mut clocks = Vec::new();
        for s in structs.iter().filter(|s| s.kind != Kind::Skip) {
            clocks.extend((s.clock..s.clock + s.len).map(|clock| (s.client, clock)));
        }
        clocks.sort_unstable();
        let mut once = clocks.clone();
        once.dedup();
        assert_eq!(clocks, once, "a clock is encoded twice");
        let mut deleted_clocks = Vec::new();
        for (client, clock, len) in deleted {
            deleted_clocks.extend((clock..clock + len).map(|clock| (client, clock)));
        }
        deleted_clocks.sort_unstable();
        deleted_clocks.dedup();
        (clocks, deleted_clocks)
    };
    let once = waiting(&s.peers[1]);
    assert_eq!(once.0, [(1, 2), (1, 3), (1, 4)]);
    assert_eq!(once.1, [(1, 0), (1, 4)]);
    // the steps after which a replica waits for exactly these clocks
    let mut waits = vec![s.steps.len() - 1];
    // the same updates again, in another order
    for index in [3, 1, 2, 2] {
        s.deliver(0, 1, index);
        assert_eq!(waiting(&s.peers[1]), once, "a duplicate changed what waits");
        waits.push(s.steps.len() - 1);
    }
    // replica 2 gets what waits from replica 1, twice, by both kinds of diff
    s.sync_by_model(1, 2);
    assert!(s.peers[2].doc.has_pending_updates());
    assert_eq!(waiting(&s.peers[2]), once);
    waits.push(s.steps.len() - 1);
    s.sync_by_model(1, 2);
    waits.push(s.steps.len() - 1);
    s.sync(1, 2);
    assert_eq!(waiting(&s.peers[2]), once, "a repeated sync changed what waits");
    waits.push(s.steps.len() - 1);
    // and back: replica 1 learns nothing new
    s.sync_by_model(2, 1);
    assert_eq!(waiting(&s.peers[1]), once);
    assert_eq!(s.peers[1].text.to_string(), "");
    waits.push(s.steps.len() - 1);
    // the model, before the missing update arrives: the clocks of the structs
    // and of the deletions it would send on, each as often as it holds it
    if let Some(bin) = spec_bin() {
        let model = run_model(&bin, &s.name, &s.trace());
        let clocks = |ranges: &Json| {
            let mut clocks = Vec::new();
            for range in ranges.as_array().unwrap() {
                let field = |index: usize| range[index].as_u64().unwrap();
                clocks.extend((field(1)..field(1) + field(2)).map(|clock| (field(0), clock)));
            }
            clocks.sort_unstable();
            clocks
        };
        for &step in &waits {
            let snapshot = &model["steps"][step];
            assert_eq!(snapshot["pending"], json!(true), "step {step}: the model does not wait");
            assert_eq!(
                clocks(&snapshot["export"]["structs"]),
                once.0,
                "step {step}: the model holds a waiting struct clock other than once"
            );
            assert_eq!(
                clocks(&snapshot["export"]["ds"]),
                once.1,
                "step {step}: the model holds a waiting deletion other than once"
            );
        }
    }
    // the missing update arrives: every clock once
    for replica in [1, 2] {
        s.deliver(0, replica, 0);
        assert!(!s.peers[replica].doc.has_pending_updates());
        assert_eq!(s.peers[replica].text.to_string(), s.peers[0].text.to_string());
        let ids = s.peers[replica].snapshot()["ids"].clone();
        assert_eq!(ids, s.peers[0].snapshot()["ids"]);
        assert_eq!(s.peers[replica].snapshot()["sv"], json!([[1, 5]]));
    }
    // once more, now that nothing waits
    s.sync_by_model(1, 2);
    s.sync_by_model(2, 1);
    s.settle();
    check(s);
}

/// A `Node::GC` struct counts as deleted in the delete set, also when the
/// model sends it on in a state diff.
#[test]
#[cfg_attr(miri, ignore = "Differential scenarios run in ordinary tests")]
fn gc_struct_counts_as_deleted_like_in_the_lean_model() {
    let mut s = Scenario::new("gc struct", &[(1, false), (2, true), (3, false)]);
    for replica in 0..2 {
        // one client (7) with one struct: a GC of 4 clocks from clock 0;
        // empty delete set
        s.apply(replica, &[1, 1, 7, 0, 0, 4, 0]);
        let snapshot = s.peers[replica].snapshot();
        assert_eq!(snapshot["sv"], json!([[7, 4]]));
        assert_eq!(snapshot["ds"], json!([[7, 0, 4]]));
        assert_eq!(snapshot["pending"], json!(false));
    }
    s.insert(0, 0, "x");
    s.sync_by_model(0, 2);
    let snapshot = s.peers[2].snapshot();
    assert_eq!(snapshot["sv"], json!([[1, 1], [7, 4]]));
    assert_eq!(snapshot["ds"], json!([[7, 0, 4]]));
    s.settle();
    check(s);
}

/// The `gcNode` step of the model (no y-octo counterpart on a root text)
/// turns a deleted block into a `Node::GC`: delete set and state vector stay.
#[test]
#[cfg_attr(miri, ignore = "Differential scenarios run in ordinary tests")]
fn gc_node_step_keeps_delete_set_and_state_vector() {
    let Some(bin) = spec_bin() else {
        eprintln!("YOCTO_SPEC_BIN is not set: the gcNode step of the model was not run");
        return;
    };
    let trace = json!({
        "replicas": [{"client": 1, "gc": false}],
        "steps": [
            {"op": "insert", "replica": 0, "after": null, "text": "abc"},
            {"op": "delete", "replica": 0, "ranges": [[1, 1, 1]]},
            {"op": "gcNode", "replica": 0, "index": 1},
        ],
    });
    let model = run_model(&bin, "gc node", &trace);
    for step in [1, 2] {
        let state = &model["steps"][step];
        assert_eq!(state["text"], json!("ac"), "step {step}");
        assert_eq!(state["sv"], json!([[1, 3]]), "step {step}");
        assert_eq!(state["ds"], json!([[1, 1, 1]]), "step {step}");
    }
    assert_eq!(model["steps"][1]["gc"], json!([]));
    assert_eq!(model["steps"][2]["gc"], json!([[1, 1, 1]]));
    assert_eq!(model["steps"][2]["order"], json!([[1, 0], [1, 2]]));
}
