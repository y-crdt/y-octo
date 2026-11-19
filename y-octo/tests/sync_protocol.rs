//! `y-protocols/sync` handshake through [Doc::sync_step1] and
//! [Doc::handle_doc_message], with replicas that go offline and synchronize
//! late, ported from the Yjs `testHelper.ts` connector scenarios.

use std::{
    collections::VecDeque,
    hash::{Hash, Hasher},
    sync::{
        Arc, Mutex,
        atomic::{AtomicUsize, Ordering},
    },
};

use rand::{RngExt, SeedableRng};
use rand_chacha::ChaCha20Rng;
use y_octo::{
    Any, Doc, DocMessage, DocOptions, JwstCodecError, Origin, StateVector, Subscription, SyncMessage,
    SyncMessageScanner, Value, read_doc_message, read_sync_message, write_doc_message, write_sync_message,
};

fn doc(client: u64) -> Doc {
    DocOptions::from_identity(client, "sync".into()).build()
}

fn frame(msg: &DocMessage) -> Vec<u8> {
    let mut buffer = Vec::new();
    write_sync_message(&mut buffer, &SyncMessage::Doc(msg.clone())).unwrap();
    buffer
}

fn unframe(bytes: &[u8]) -> DocMessage {
    let (tail, msg) = read_sync_message(bytes).unwrap();
    assert!(tail.is_empty());
    let SyncMessage::Doc(msg) = msg else {
        panic!("not a document message: {msg:?}");
    };
    msg
}

/// Local commit updates of `doc`, as a provider would broadcast them.
fn record(doc: &Doc) -> (Subscription, Arc<Mutex<Vec<Vec<u8>>>>) {
    let updates = Arc::new(Mutex::new(Vec::new()));
    let sink = updates.clone();
    let subscription = doc.subscribe(move |event| {
        if event.local {
            sink.lock().unwrap().push(event.update.clone());
        }
    });
    (subscription, updates)
}

// Frames of y-protocols@1.0.6 with Yjs@13.6.33 for the same edits.
const UPDATE_AB: &[u8] = &[0, 2, 12, 1, 1, 7, 0, 4, 1, 1, 116, 2, 97, 98, 0];
const STEP1_SEEN_AB: &[u8] = &[0, 0, 3, 1, 7, 2];
const STEP2_DELETE_A: &[u8] = &[0, 1, 6, 0, 1, 7, 1, 0, 1];
const STEP1_TWO_CLIENTS: &[u8] = &[0, 5, 2, 7, 4, 1, 2];

#[test]
fn sync_frames_match_pinned_y_protocols_on_equal_clock_reconnect() {
    let a = doc(7);
    let mut b = doc(2);
    let (_recording, updates) = record(&a);
    let mut text = a.get_or_create_text("t").unwrap();
    text.insert(0, "ab").unwrap();
    let [update]: [Vec<u8>; 1] = std::mem::take(&mut *updates.lock().unwrap()).try_into().unwrap();
    assert_eq!(update, a.encode_update_v1().unwrap());
    let update = frame(&DocMessage::Update(update));
    assert_eq!(update, UPDATE_AB);
    assert_eq!(b.handle_doc_message(&unframe(&update)).unwrap(), None);
    assert_eq!(b.get_or_create_text("t").unwrap().to_string(), "ab");

    // offline, `a` deletes 'a': both state vectors stay equal, only the
    // delete set tells them apart
    text.remove(0, 1).unwrap();
    assert_eq!(a.get_state_vector(), b.get_state_vector());
    assert_eq!(b.get_or_create_text("t").unwrap().to_string(), "ab");

    let step1 = frame(&b.sync_step1().unwrap());
    assert_eq!(step1, STEP1_SEEN_AB);
    let step2 = a
        .handle_doc_message_with_origin(&unframe(&step1), None)
        .unwrap()
        .unwrap();
    let step2 = frame(&step2);
    assert_eq!(step2, STEP2_DELETE_A);
    assert_eq!(b.handle_doc_message(&unframe(&step2)).unwrap(), None);

    // the other direction has nothing new left
    let mut a_mut = a.clone();
    let reply = b.handle_doc_message(&a.sync_step1().unwrap()).unwrap().unwrap();
    assert_eq!(a_mut.handle_doc_message(&reply).unwrap(), None);

    assert_eq!(a.get_or_create_text("t").unwrap().to_string(), "b");
    assert_eq!(b.get_or_create_text("t").unwrap().to_string(), "b");
    assert!(a.store_compare(&b));
    assert_eq!(a.get_delete_sets(), b.get_delete_sets());
    assert_eq!(a.encode_update_v1().unwrap(), b.encode_update_v1().unwrap());

    // state vectors are written with clients in descending order
    let mut first = doc(1);
    first.get_or_create_text("t").unwrap().insert(0, "xy").unwrap();
    let second = doc(7);
    second.get_or_create_text("t").unwrap().insert(0, "pqrs").unwrap();
    first
        .apply_update_from_binary_v1(second.encode_update_v1().unwrap())
        .unwrap();
    let mut buffer = Vec::new();
    write_doc_message(&mut buffer, &first.sync_step1().unwrap()).unwrap();
    assert_eq!(buffer, STEP1_TWO_CLIENTS);
    let (tail, DocMessage::Step1(sv)) = read_doc_message(&buffer).unwrap() else {
        panic!("not a step 1 message");
    };
    assert!(tail.is_empty());
    assert_eq!(StateVector::decode_v1(sv).unwrap(), first.get_state_vector());
}

/// An origin whose destructor reads the document: dropped under the
/// document lock, it fails with a reentrance error.
#[derive(Clone)]
struct DropProbe {
    doc: Doc,
    drops: Arc<AtomicUsize>,
}

impl PartialEq for DropProbe {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.drops, &other.drops)
    }
}

impl Eq for DropProbe {}

impl Hash for DropProbe {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.drops).hash(state);
    }
}

impl Drop for DropProbe {
    fn drop(&mut self) {
        let _ = self.doc.get_state_vector();
        let _ = self.doc.keys();
        self.drops.fetch_add(1, Ordering::SeqCst);
    }
}

#[test]
fn handle_doc_message_propagates_origin_and_drops_outside_lock() {
    let local = doc(1);
    let remote = doc(2);
    let mut remote_text = remote.get_or_create_text("text").unwrap();
    remote_text.insert(0, "hello").unwrap();

    let drops = Arc::new(AtomicUsize::new(0));
    let probe = || {
        Origin::new(DropProbe {
            doc: local.clone(),
            drops: drops.clone(),
        })
    };

    // a provider broadcasts local commits and skips what it applied itself
    let synced = Arc::new(AtomicUsize::new(0));
    let outbox = Arc::new(Mutex::new(Vec::new()));
    let _provider = {
        let synced = synced.clone();
        let outbox = outbox.clone();
        local.subscribe(move |event| {
            if event
                .origin
                .as_ref()
                .and_then(|o| o.downcast_ref::<DropProbe>())
                .is_some()
            {
                assert!(!event.local);
                synced.fetch_add(1, Ordering::SeqCst);
            } else {
                outbox.lock().unwrap().push(DocMessage::Update(event.update.clone()));
            }
        })
    };

    let reply = local
        .handle_doc_message_with_origin(&remote.sync_step1().unwrap(), probe())
        .unwrap();
    assert!(matches!(reply, Some(DocMessage::Step2(_))));
    assert_eq!(drops.load(Ordering::SeqCst), 1);

    let step2 = remote.sync_step2(&local.get_state_vector()).unwrap();
    assert_eq!(local.handle_doc_message_with_origin(&step2, probe()).unwrap(), None);
    assert_eq!(drops.load(Ordering::SeqCst), 2);
    assert_eq!(local.get_or_create_text("text").unwrap().to_string(), "hello");

    let (_recording, updates) = record(&remote);
    remote_text.insert(5, "!").unwrap();
    let [update]: [Vec<u8>; 1] = std::mem::take(&mut *updates.lock().unwrap()).try_into().unwrap();
    assert_eq!(
        local
            .handle_doc_message_with_origin(&DocMessage::Update(update), probe())
            .unwrap(),
        None
    );
    assert_eq!(drops.load(Ordering::SeqCst), 3);
    assert_eq!(local.get_or_create_text("text").unwrap().to_string(), "hello!");

    let mut sv = remote.get_state_vector().encode_v1().unwrap();
    sv.push(0);
    assert_eq!(
        local.handle_doc_message_with_origin(&DocMessage::Step1(sv), probe()),
        Err(JwstCodecError::UpdateNotFullyConsumed(1))
    );
    assert_eq!(drops.load(Ordering::SeqCst), 4);

    let mut update = remote.encode_update_v1().unwrap();
    update.push(0);
    assert_eq!(
        local.handle_doc_message_with_origin(&DocMessage::Step2(update), probe()),
        Err(JwstCodecError::UpdateNotFullyConsumed(1))
    );
    assert_eq!(drops.load(Ordering::SeqCst), 5);

    // synchronized commits are not echoed back, local edits are
    assert_eq!(synced.load(Ordering::SeqCst), 2);
    assert!(outbox.lock().unwrap().is_empty());
    local.get_or_create_text("text").unwrap().insert(0, ">").unwrap();
    let [echo]: [DocMessage; 1] = std::mem::take(&mut *outbox.lock().unwrap()).try_into().unwrap();
    let mut peer = remote.clone();
    assert_eq!(peer.handle_doc_message(&echo).unwrap(), None);
    assert_eq!(remote_text.to_string(), ">hello!");
}

/// The delete set of the whole document as it goes on the wire (an update
/// without structs), built from the deleted structs of the store.
fn wire_delete_set(doc: &Doc) -> Vec<u8> {
    doc.encode_state_as_update_v1(&doc.get_state_vector()).unwrap()
}

#[derive(Default)]
struct Network {
    online: Vec<bool>,
    /// Frames waiting for each replica, with the replica that sent them.
    inboxes: Vec<VecDeque<(usize, Vec<u8>)>>,
}

/// Replicas exchanging `y-protocols/sync` frames: local commits go to every
/// other online replica, connecting runs the step 1 / step 2 handshake with
/// each of them. Disconnecting drops what the replica has not read yet but
/// keeps its subscription, so it resumes broadcasting once it reconnects.
struct TestConnector {
    docs: Vec<Doc>,
    network: Arc<Mutex<Network>>,
    origin: Origin,
    _subscriptions: Vec<Subscription>,
}

impl TestConnector {
    fn new(replicas: usize) -> Self {
        let network = Arc::new(Mutex::new(Network {
            online: vec![false; replicas],
            inboxes: vec![VecDeque::new(); replicas],
        }));
        let origin = Origin::new("connector");
        let mut docs = Vec::new();
        let mut subscriptions = Vec::new();
        for (index, client) in (1..=replicas as u64).enumerate() {
            let doc = DocOptions::from_identity(client, "connector".into()).build();
            doc.get_or_create_array("array").unwrap();
            doc.get_or_create_map("map").unwrap();
            doc.get_or_create_text("text").unwrap();
            let network = network.clone();
            let connector = origin.clone();
            subscriptions.push(doc.subscribe(move |event| {
                if event.origin.as_ref() == Some(&connector) {
                    return;
                }
                let mut network = network.lock().unwrap();
                if !network.online[index] {
                    return;
                }
                let update = frame(&DocMessage::Update(event.update.clone()));
                for peer in 0..replicas {
                    if peer != index && network.online[peer] {
                        network.inboxes[peer].push_back((index, update.clone()));
                    }
                }
            }));
            docs.push(doc);
        }
        let mut connector = Self {
            docs,
            network,
            origin,
            _subscriptions: subscriptions,
        };
        for index in 0..replicas {
            connector.connect(index);
        }
        connector
    }

    fn len(&self) -> usize {
        self.docs.len()
    }

    fn online(&self, index: usize) -> bool {
        self.network.lock().unwrap().online[index]
    }

    fn pending(&self, index: usize) -> usize {
        self.network.lock().unwrap().inboxes[index].len()
    }

    fn connect(&mut self, index: usize) {
        let mut network = self.network.lock().unwrap();
        if network.online[index] {
            return;
        }
        network.online[index] = true;
        let step1 = frame(&self.docs[index].sync_step1().unwrap());
        for peer in 0..self.len() {
            if peer != index && network.online[peer] {
                network.inboxes[peer].push_back((index, step1.clone()));
                let reply = frame(&self.docs[peer].sync_step1().unwrap());
                network.inboxes[index].push_back((peer, reply));
            }
        }
    }

    fn disconnect(&mut self, index: usize) {
        let mut network = self.network.lock().unwrap();
        network.online[index] = false;
        network.inboxes[index].clear();
    }

    fn connect_all(&mut self) {
        for index in 0..self.len() {
            self.connect(index);
        }
    }

    fn receive(&self, to: usize, from: usize, msg: DocMessage) {
        let reply = self.docs[to]
            .handle_doc_message_with_origin(&msg, self.origin.clone())
            .unwrap();
        if let Some(reply) = reply {
            let mut network = self.network.lock().unwrap();
            if network.online[from] {
                network.inboxes[from].push_back((to, frame(&reply)));
            }
        }
    }

    /// Delivers the oldest frame waiting for `to`.
    fn deliver_one(&self, to: usize) -> bool {
        let next = self.network.lock().unwrap().inboxes[to].pop_front();
        let Some((from, bytes)) = next else {
            return false;
        };
        self.receive(to, from, unframe(&bytes));
        true
    }

    /// Delivers every frame waiting for `to`, each sender's consecutive
    /// frames read back from one byte stream.
    fn deliver_batch(&self, to: usize) -> bool {
        let frames = std::mem::take(&mut self.network.lock().unwrap().inboxes[to]);
        let mut batches: Vec<(usize, Vec<u8>)> = Vec::new();
        for (from, bytes) in frames {
            match batches.last_mut() {
                Some((sender, stream)) if *sender == from => stream.extend_from_slice(&bytes),
                _ => batches.push((from, bytes)),
            }
        }
        let delivered = !batches.is_empty();
        for (from, stream) in batches {
            for msg in SyncMessageScanner::new(&stream) {
                let SyncMessage::Doc(msg) = msg.unwrap() else {
                    panic!("not a document message");
                };
                self.receive(to, from, msg);
            }
        }
        delivered
    }

    fn flush(&self) {
        loop {
            let mut delivered = false;
            for index in 0..self.len() {
                while self.deliver_one(index) {
                    delivered = true;
                }
            }
            if !delivered {
                break;
            }
        }
    }

    fn doc(&self, index: usize) -> &Doc {
        &self.docs[index]
    }

    fn array(&self, index: usize) -> serde_json::Value {
        serde_json::to_value(self.docs[index].get_or_create_array("array").unwrap()).unwrap()
    }

    /// Asserts that every replica is online, has read everything and holds
    /// the same content and store.
    fn compare_all(&self) {
        for index in 0..self.len() {
            assert!(self.online(index), "replica {index} is offline");
            assert_eq!(self.pending(index), 0, "replica {index} has unread frames");
            assert!(!self.docs[index].has_pending_updates(), "replica {index}");
        }
        let first = &self.docs[0];
        for (index, doc) in self.docs.iter().enumerate().skip(1) {
            assert_eq!(self.array(index), self.array(0), "array of replica {index}");
            assert_eq!(
                serde_json::to_value(doc.get_or_create_map("map").unwrap()).unwrap(),
                serde_json::to_value(first.get_or_create_map("map").unwrap()).unwrap(),
                "map of replica {index}"
            );
            assert_eq!(
                doc.get_or_create_text("text").unwrap().to_string(),
                first.get_or_create_text("text").unwrap().to_string(),
                "text of replica {index}"
            );
            assert_eq!(doc.get_state_vector(), first.get_state_vector(), "replica {index}");
            // `get_delete_sets` records the deletions as each replica learned
            // them; compare what the stores encode instead
            assert_eq!(wire_delete_set(doc), wire_delete_set(first), "replica {index}");
            assert!(doc.store_compare(first), "store of replica {index}");
        }
    }
}

#[test]
fn late_sync_disconnect_reconnect_and_map_clear_conflicts() {
    // insertions in late sync; a disconnected replica neither sends nor
    // receives
    {
        let mut connector = TestConnector::new(3);
        connector
            .doc(0)
            .get_or_create_array("array")
            .unwrap()
            .push("x")
            .unwrap();
        connector.flush();
        connector.disconnect(2);
        connector
            .doc(2)
            .get_or_create_array("array")
            .unwrap()
            .insert(0, "c")
            .unwrap();
        assert_eq!((connector.pending(0), connector.pending(1)), (0, 0));
        connector
            .doc(0)
            .get_or_create_array("array")
            .unwrap()
            .insert(0, "a")
            .unwrap();
        connector
            .doc(1)
            .get_or_create_array("array")
            .unwrap()
            .insert(0, "b")
            .unwrap();
        assert_eq!(connector.pending(2), 0);
        connector.flush();
        assert_eq!(connector.array(2), serde_json::json!(["c", "x"]));
        assert_eq!(connector.array(0).as_array().unwrap().len(), 3);
        assert_eq!(connector.array(0), connector.array(1));

        connector.disconnect(0);
        connector.disconnect(1);
        for index in 0..3 {
            let mut array = connector.doc(index).get_or_create_array("array").unwrap();
            array.insert(1, index as i64).unwrap();
        }
        connector.connect_all();
        connector.flush();
        connector.compare_all();
        assert_eq!(connector.array(0).as_array().unwrap().len(), 7);
    }

    // overlapping deletions in late sync
    {
        let mut connector = TestConnector::new(2);
        let mut array = connector.doc(0).get_or_create_array("array").unwrap();
        for value in 0..6 {
            array.push(value).unwrap();
        }
        connector.flush();
        connector.disconnect(0);
        connector.disconnect(1);
        array.remove(1, 2).unwrap();
        connector
            .doc(1)
            .get_or_create_array("array")
            .unwrap()
            .remove(2, 2)
            .unwrap();
        connector.connect_all();
        connector.flush();
        connector.compare_all();
        assert_eq!(connector.array(0), serde_json::json!([0, 4, 5]));
    }

    // a merged sequence deleted while the inserting replica is offline
    {
        let mut connector = TestConnector::new(2);
        let mut array = connector.doc(0).get_or_create_array("array").unwrap();
        for value in ["x", "y", "z"] {
            array.push(value).unwrap();
        }
        connector.flush();
        connector.disconnect(0);
        connector
            .doc(1)
            .get_or_create_array("array")
            .unwrap()
            .remove(0, 3)
            .unwrap();
        connector.connect(0);
        connector.flush();
        connector.compare_all();
        assert_eq!(connector.array(0), serde_json::json!([]));
    }

    // concurrent sets and clears of a map property
    {
        let connector = TestConnector::new(4);
        let map = |index: usize| connector.doc(index).get_or_create_map("map").unwrap();
        map(0).insert("stuff".into(), "c0").unwrap();
        map(1).insert("stuff".into(), "c1").unwrap();
        map(1).insert("stuff".into(), "c2").unwrap();
        map(2).insert("stuff".into(), "c3").unwrap();
        connector.flush();
        connector.compare_all();

        map(0).insert("stuff".into(), "c0").unwrap();
        map(1).clear().unwrap();
        map(1).insert("stuff".into(), "c1").unwrap();
        map(2).insert("stuff".into(), "c2").unwrap();
        map(3).insert("stuff".into(), "c3").unwrap();
        map(3).clear().unwrap();
        connector.flush();
        connector.compare_all();
        // each clear only deletes the values its replica had seen; the
        // remaining winner, if any, is one of the concurrent sets
        if let Some(value) = map(0).get("stuff") {
            assert!(
                ["c0", "c1", "c2"].map(|v| Value::Any(Any::from(v))).contains(&value),
                "{value:?}"
            );
        }
    }
}

#[cfg(not(miri))]
const RANDOM_RUNS: (&[u64], usize) = (&[1, 2, 3, 4, 5, 6, 7, 8], 120);
#[cfg(miri)]
const RANDOM_RUNS: (&[u64], usize) = (&[1], 20);

#[test]
fn multi_peer_random_sync_reconnect_converges() {
    let (seeds, steps) = RANDOM_RUNS;
    for &seed in seeds {
        let mut rng = ChaCha20Rng::seed_from_u64(seed);
        let mut connector = TestConnector::new(5);
        for _ in 0..steps {
            let index = rng.random_range(0..connector.len());
            let doc = connector.doc(index).clone();
            let mut array = doc.get_or_create_array("array").unwrap();
            let mut map = doc.get_or_create_map("map").unwrap();
            let mut text = doc.get_or_create_text("text").unwrap();
            let key = format!("k{}", rng.random_range(0..4));
            match rng.random_range(0..100) {
                0..15 => {
                    let at = rng.random_range(0..=array.len());
                    array.insert(at, rng.random_range(0..1000i64)).unwrap();
                }
                15..22 if !array.is_empty() => {
                    let at = rng.random_range(0..array.len());
                    let len = rng.random_range(1..=(array.len() - at).min(3));
                    array.remove(at, len).unwrap();
                }
                22..34 => map.insert(key, rng.random_range(0..1000i64)).unwrap(),
                34..40 => map.remove(&key),
                40..43 => map.clear().unwrap(),
                43..58 => {
                    let at = rng.random_range(0..=text.len());
                    let ch = char::from(b'a' + rng.random_range(0..26u8));
                    text.insert(at, ch.to_string().repeat(rng.random_range(1..4))).unwrap();
                }
                58..65 if !text.is_empty() => {
                    let at = rng.random_range(0..text.len());
                    let len = rng.random_range(1..=(text.len() - at).min(3));
                    text.remove(at, len).unwrap();
                }
                65..80 => {
                    connector.deliver_one(index);
                }
                80..88 => {
                    connector.deliver_batch(index);
                }
                88..94 => connector.disconnect(index),
                94..100 if !connector.online(index) => connector.connect(index),
                _ => {}
            }
        }
        connector.connect_all();
        connector.flush();
        connector.compare_all();
    }
}
