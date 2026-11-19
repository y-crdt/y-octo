//! Without the `random` feature the host assigns client IDs (0 is an ordinary
//! one): a subdocument projection (its options carry no ID), or a document
//! whose ID a remote replica turned out to use, refuses local writes until the
//! host sets one.

use super::*;

fn doc(client: Client) -> Doc {
    DocOptions::from_identity(client, "identity".into()).build()
}

fn sync(from: &Doc, to: &Doc) {
    to.apply_update_with_origin(
        from.encode_state_as_update(&to.get_state_vector()).unwrap(),
        Origin::new("remote"),
    )
    .unwrap();
}

#[test]
fn distinct_client_ids_never_require_a_new_one() {
    let (a, b) = (doc(7), doc(8));
    let mut text_a = a.get_or_create_text("text").unwrap();
    let mut text_b = b.get_or_create_text("text").unwrap();
    text_a.insert(0, "a").unwrap();
    text_b.insert(0, "b").unwrap();
    sync(&a, &b);
    sync(&b, &a);
    assert!(!a.client_required() && !b.client_required());
    assert_eq!(text_a.to_string(), text_b.to_string());
    assert_eq!((a.client(), b.client()), (7, 8));
}

/// Two receivers share the author's client ID and reach the same clocks: both
/// have to get a new ID from the host, none is derived.
#[test]
fn replicas_using_the_same_client_id_wait_for_the_host() {
    let author = doc(7);
    let (mut b, mut c) = (doc(7), doc(7));
    author.get_or_create_text("text").unwrap().insert(0, "hello").unwrap();
    let mut text_b = b.get_or_create_text("text").unwrap();
    let mut text_c = c.get_or_create_text("text").unwrap();
    sync(&author, &b);
    sync(&author, &c);

    for (replica, text) in [(&b, &mut text_b), (&c, &mut text_c)] {
        assert!(replica.client_required());
        assert_eq!(replica.client(), 7, "kept until the host decides");
        assert_eq!(text.insert(5, "!"), Err(JwstCodecError::ClientIdRequired));
        assert_eq!(text.to_string(), "hello", "remote content is applied");
        // remote updates keep arriving
        sync(&author, replica);
    }

    b.set_client(8);
    c.set_client(9);
    assert!(!b.client_required() && !c.client_required());
    text_b.insert(5, " b").unwrap();
    text_c.insert(5, " c").unwrap();
    for (from, to) in [
        (&b, &author),
        (&c, &author),
        (&author, &b),
        (&author, &c),
        (&b, &c),
        (&c, &b),
    ] {
        sync(from, to);
    }
    let text = author.get_or_create_text("text").unwrap().to_string();
    assert_eq!(text_b.to_string(), text);
    assert_eq!(text_c.to_string(), text);
    assert!(!author.client_required(), "the author's own ID is not taken");
}

/// A subdocument read from a document has no client ID of its own here.
#[test]
fn subdocument_projections_wait_for_the_host() {
    let parent = doc(7);
    let mut map = parent.get_or_create_map("map").unwrap();
    map.insert("sub".into(), Value::Doc(doc(7))).unwrap();
    let Some(Value::Doc(mut sub)) = map.get("sub") else {
        panic!("not a subdocument");
    };
    assert_eq!(sub.client(), 0);
    assert!(sub.client_required());
    let mut text = sub.get_or_create_text("text").unwrap();
    assert_eq!(text.insert(0, "a"), Err(JwstCodecError::ClientIdRequired));
    sub.set_client(11);
    text.insert(0, "a").unwrap();
}

/// `Map::remove` returns nothing (kept for compatibility) and panics with
/// `ClientIdRequired`; the recoverable path is a transaction, whose entry
/// returns the error before anything changes, and which the host retries
/// after `set_client`.
#[test]
fn map_removal_while_the_host_assigns_an_id() {
    let author = doc(7);
    author.get_or_create_map("map").unwrap().insert("k".into(), 1).unwrap();
    let mut b = doc(7);
    let mut map = b.get_or_create_map("map").unwrap();
    sync(&author, &b);
    assert!(b.client_required());
    let before = b.encode_update_v1().unwrap();

    let remove = |b: &Doc, map: &Map| {
        b.transact_mut(None, |tx| {
            tx.map(map)?.remove("k");
            Ok(())
        })
    };
    assert_eq!(remove(&b, &map), Err(JwstCodecError::ClientIdRequired));
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| map.remove("k"))).unwrap_err();
    assert_eq!(
        panic.downcast_ref::<String>().map(String::as_str),
        Some(JwstCodecError::ClientIdRequired.to_string().as_str())
    );
    assert_eq!(b.encode_update_v1().unwrap(), before, "nothing changed");
    assert!(map.contains_key("k"));

    b.set_client(8);
    remove(&b, &map).unwrap();
    assert!(!map.contains_key("k"));
    sync(&b, &author);
    assert!(!author.get_or_create_map("map").unwrap().contains_key("k"));
}

/// Without the host's assignment the document waits: a subdocument
/// projection, or a collision. Any client ID the host sets, 0 included, makes
/// it writable; one the host passes is never questioned, 0 included.
#[test]
fn only_identities_the_host_did_not_assign_wait() {
    let zero = doc(0);
    assert!(!zero.client_required(), "0 from the host is an identity");
    zero.get_or_create_text("text").unwrap().insert(0, "a").unwrap();
    assert_eq!(zero.get_state_vector(), StateVector::from([(0, 1)]));

    let parent = doc(7);
    let mut map = parent.get_or_create_map("map").unwrap();
    map.insert("sub".into(), Value::Doc(doc(9))).unwrap();
    let Some(Value::Doc(mut projected)) = map.get("sub") else {
        panic!("not a subdocument");
    };
    let mut collided = doc(0);
    sync(&zero, &collided);

    for replica in [&mut projected, &mut collided] {
        assert!(replica.client_required());
        let mut text = replica.get_or_create_text("text").unwrap();
        assert_eq!(text.insert(0, "x"), Err(JwstCodecError::ClientIdRequired));
        replica.set_client(0);
        assert!(!replica.client_required(), "the host chose 0");
        text.insert(0, "x").unwrap();
    }
    assert_eq!(projected.get_state_vector(), StateVector::from([(0, 1)]));
    assert_eq!(
        collided.get_state_vector(),
        StateVector::from([(0, 2)]),
        "the host reused the colliding ID on purpose"
    );
}

fn content(doc: &Doc, id: (Client, Clock)) -> Content {
    let store = doc.store.read().unwrap();
    match store.get_node(id).unwrap() {
        Node::Item(item) => item.get().unwrap().content.clone(),
        node => panic!("{id:?} is {node:?}"),
    }
}

/// While the host has to assign a client ID, undo and redo (they create
/// structs) are refused, but the manager's bookkeeping runs: clearing,
/// dropping (also inside a transaction, released after it) and a new manager.
#[test]
fn undo_bookkeeping_runs_while_the_host_assigns_an_id() {
    let author = doc(1);
    author.get_or_create_text("text").unwrap().insert(0, "abc").unwrap();
    let mut b = doc(7);
    let mut text = b.get_or_create_text("text").unwrap();
    sync(&author, &b);
    let undo = UndoManager::<()>::new(&b, [(&text).into()], UndoOptions::default()).unwrap();
    text.remove(1, 1).unwrap(); // retained "b"
    assert_eq!(content(&b, (1, 1)), Content::String("b".into()));

    // another replica writes with client ID 7
    let other = doc(7);
    sync(&author, &other);
    other.get_or_create_text("text").unwrap().insert(0, "zz").unwrap();
    sync(&other, &b);
    assert!(b.client_required());

    assert_eq!(undo.undo().unwrap_err(), JwstCodecError::ClientIdRequired);
    undo.stop_capturing().unwrap();
    undo.clear(true, true).unwrap();
    assert_eq!(content(&b, (1, 1)), Content::Deleted(1), "released");
    drop(undo);
    assert!(
        b.store.read().unwrap().history_hook.is_none(),
        "dropped outside a transaction"
    );

    let undo = UndoManager::<()>::new(&b, [(&text).into()], UndoOptions::default()).unwrap();
    b.transact(|_| drop(undo)).unwrap();
    assert!(
        b.store.read().unwrap().history_hook.is_none(),
        "released after the read lock"
    );
    let undo = UndoManager::<()>::new(&b, [(&text).into()], UndoOptions::default()).unwrap();

    b.set_client(8);
    text.insert(0, "x").unwrap();
    assert!(undo.undo().unwrap().is_some());
    assert_eq!(text.to_string(), "zzac");
}
