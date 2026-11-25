//! A timeline that is full: an edit of several blocks is refused whole, with
//! the document as it was, and is taken as soon as every timeline it touches
//! has room for exactly its blocks. A struct that is collected takes a block
//! and no item, so the room of the item arena says nothing about this.
use super::*;

/// Collected ranges and gaps in turn at the end of the timeline of `client`,
/// until it holds `blocks` blocks: neighbours of two kinds, which a commit
/// does not make one block of.
fn pad(doc: &Doc, client: Client, blocks: usize) {
    let mut store = doc.store.write().unwrap();
    loop {
        let (len, last) = store.items.get(&client).map_or((0, None), |timeline| {
            (
                timeline.len(),
                timeline.len().checked_sub(1).map(|i| timeline.kind_at(i)),
            )
        });
        if len >= blocks {
            break;
        }
        let id = Id::new(client, store.get_state(client));
        let node = if last == Some(BlockKind::Gc) {
            Node::new_skip(id, 1)
        } else {
            Node::new_gc(id, 1)
        };
        store.add_node(node).unwrap();
    }
}

fn blocks(doc: &Doc, client: Client) -> usize {
    doc.store
        .read()
        .unwrap()
        .items
        .get(&client)
        .map_or(0, |timeline| timeline.len())
}

fn refused<T: std::fmt::Debug>(result: JwstCodecResult<T>) {
    assert!(
        matches!(result, Err(JwstCodecError::IncompleteDocument(_))),
        "{result:?}"
    );
}

#[test]
fn a_timeline_takes_blocks_up_to_its_limit() {
    let mut timeline = ClientBlocks::default();
    let block = |clock| BlockRef {
        clock,
        kind: BlockKind::Gc,
    };
    let _limit = ClientBlocks::set_limit(3);
    assert_eq!(ClientBlocks::limit(), 3);
    for clock in 0..3 {
        assert_eq!(timeline.check_capacity(3 - clock as usize), Ok(()));
        refused(timeline.check_capacity(4 - clock as usize));
        timeline.append(block(clock), 1).unwrap();
    }
    assert!(timeline.is_full());
    assert_eq!(timeline.check_capacity(0), Ok(()));
    refused(timeline.check_capacity(1));
    refused(timeline.check_capacity(usize::MAX));
    refused(timeline.check_append(3, 1));
    refused(timeline.append(block(3), 1));
    assert_eq!(timeline.len(), 3);
    assert_eq!(timeline.end_clock(), 3);
    drop(_limit);
    assert_eq!(ClientBlocks::limit(), u32::MAX as usize);
    timeline.append(block(3), 1).unwrap();
}

#[test]
fn a_mount_at_a_full_timeline_is_refused_whole_and_fits_exactly() {
    let doc = Doc::with_client(101);
    let mut map = doc.get_or_create_map("map").unwrap();
    let mut root = doc.get_or_create_array("root").unwrap();
    for key in ["a", "b", "c"] {
        map.insert(key.into(), 1).unwrap();
        let mut store = doc.store.write().unwrap();
        let clock = store.get_state(101);
        store.add_node(Node::new_gc(Id::new(101, clock), 1)).unwrap();
    }
    map.insert("d".into(), 1).unwrap();
    let mut child = doc.create_array().unwrap();
    child.push(1).unwrap();
    assert_eq!(blocks(&doc, 101), 7);
    // the arena has room for the carrier and the value: the timeline has not
    doc.store.read().unwrap().type_arena.items.check_capacity(2).unwrap();
    let before = (doc.encode_update_v1().unwrap(), doc.get_state_vector());

    let limit = ClientBlocks::set_limit(8);
    refused(root.push(child.clone()));
    assert_eq!((root.len(), child.id(), child.len()), (0, None, 1));
    assert_eq!((doc.encode_update_v1().unwrap(), doc.get_state_vector()), before);
    assert_eq!(blocks(&doc, 101), 7);
    doc.store.read().unwrap().self_check().unwrap();
    drop(limit);

    // room for exactly the carrier and the value
    let _limit = ClientBlocks::set_limit(9);
    root.push(child.clone()).unwrap();
    assert_eq!((root.len(), child.len()), (1, 1));
    assert!(child.id().is_some());
    assert_eq!(blocks(&doc, 101), 9);
    doc.store.read().unwrap().self_check().unwrap();
    refused(root.push(2));
}

#[test]
fn a_map_value_mount_at_a_full_timeline_is_refused_whole() {
    let doc = Doc::with_client(7);
    let mut root = doc.get_or_create_map("root").unwrap();
    root.insert("x".into(), 1).unwrap();
    let mut child = doc.create_map().unwrap();
    child.insert("a".into(), 1).unwrap();
    child.insert("b".into(), 2).unwrap();
    pad(&doc, 7, 5);
    let before = doc.encode_update_v1().unwrap();
    // the carrier and two values: three blocks
    let limit = ClientBlocks::set_limit(7);
    refused(root.insert("child".into(), child.clone()));
    assert!(!root.contains_key("child"));
    assert_eq!(child.id(), None);
    assert_eq!(doc.encode_update_v1().unwrap(), before);
    doc.store.read().unwrap().self_check().unwrap();
    drop(limit);
    let _limit = ClientBlocks::set_limit(8);
    root.insert("child".into(), child.clone()).unwrap();
    assert_eq!(blocks(&doc, 7), 8);
    assert_eq!(
        serde_json::to_value(&root).unwrap(),
        serde_json::json!({"x":1,"child":{"a":1,"b":2}})
    );
}

#[test]
fn a_middle_insert_at_a_full_timeline_is_refused_whole_and_fits_exactly() {
    let doc = Doc::with_client(101);
    let mut map = doc.get_or_create_map("map").unwrap();
    let mut text = doc.get_or_create_text("text").unwrap();
    text.insert(0, "😀").unwrap();
    for key in ["a", "b", "c"] {
        {
            let mut store = doc.store.write().unwrap();
            let clock = store.get_state(101);
            store.add_node(Node::new_gc(Id::new(101, clock), 1)).unwrap();
        }
        map.insert(key.into(), 1).unwrap();
    }
    assert_eq!(blocks(&doc, 101), 7);
    doc.store.read().unwrap().type_arena.items.check_capacity(2).unwrap();
    let before = doc.encode_update_v1().unwrap();

    // the cut of the pair and the new item: two blocks
    let limit = ClientBlocks::set_limit(8);
    refused(text.insert(1, "x"));
    assert_eq!(text.to_string(), "😀");
    assert_eq!(doc.encode_update_v1().unwrap(), before);
    assert_eq!(blocks(&doc, 101), 7);
    doc.store.read().unwrap().self_check().unwrap();
    // an insert at the end cuts nothing: one block
    text.insert(2, "!").unwrap();
    assert_eq!(blocks(&doc, 101), 8);
    refused(text.insert(3, "?"));
    drop(limit);

    let _limit = ClientBlocks::set_limit(10);
    text.insert(1, "x").unwrap();
    assert_eq!(blocks(&doc, 101), 10);
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn a_formatted_insert_at_a_full_timeline_is_refused_whole() {
    let doc = Doc::with_client(3);
    let mut text = doc.get_or_create_text("text").unwrap();
    text.insert(0, "abcd").unwrap();
    pad(&doc, 3, 4);
    let bold = || TextAttributes::from([("bold".into(), Any::True)]);
    let before = (text.to_delta(), doc.encode_update_v1().unwrap());
    // the cut, the opening and the closing mark, the text: four blocks
    let limit = ClientBlocks::set_limit(7);
    refused(text.apply_delta(&[
        TextDeltaOp::Retain {
            retain: 2,
            format: None,
        },
        TextDeltaOp::Insert {
            insert: TextInsert::Text("X".into()),
            format: Some(bold()),
        },
    ]));
    // two cuts and two marks
    refused(text.format(1, 2, bold()));
    assert_eq!((text.to_delta(), doc.encode_update_v1().unwrap()), before);
    assert_eq!(blocks(&doc, 3), 4);
    doc.store.read().unwrap().self_check().unwrap();
    drop(limit);
    let _limit = ClientBlocks::set_limit(8);
    text.format(1, 2, bold()).unwrap();
    assert_eq!(blocks(&doc, 3), 8);
    assert_eq!(text.to_string(), "abcd");
}

/// A document of client 2 that holds the text "abcd" of client 1.
fn two_clients() -> (Doc, Text) {
    let source = Doc::with_client(1);
    source.get_or_create_text("text").unwrap().insert(0, "abcd").unwrap();
    let mut doc = Doc::with_client(2);
    doc.apply_update_from_binary_v1(source.encode_update_v1().unwrap())
        .unwrap();
    let text = doc.get_or_create_text("text").unwrap();
    (doc, text)
}

#[test]
fn the_timeline_that_is_cut_and_the_one_that_grows_are_asked_apart() {
    // the timeline of the other client is full, the local one has room
    let (doc, mut text) = two_clients();
    text.insert(4, "e").unwrap();
    pad(&doc, 1, 5);
    assert_eq!((blocks(&doc, 1), blocks(&doc, 2)), (5, 1));
    let limit = ClientBlocks::set_limit(5);
    // at the end of the text: a local block, which the commit makes one
    // with the block before it, and no cut
    text.insert(5, "f").unwrap();
    assert_eq!(text.to_string(), "abcdef");
    assert_eq!((blocks(&doc, 1), blocks(&doc, 2)), (5, 1));
    // inside the struct of the other client: its timeline takes no cut
    let before = doc.encode_update_v1().unwrap();
    refused(text.insert(2, "x"));
    refused(text.remove(1, 2));
    refused(text.format(1, 2, TextAttributes::from([("bold".into(), Any::True)])));
    assert_eq!(text.to_string(), "abcdef");
    assert_eq!(doc.encode_update_v1().unwrap(), before);
    assert_eq!((blocks(&doc, 1), blocks(&doc, 2)), (5, 1));
    doc.store.read().unwrap().self_check().unwrap();
    // a removal of the whole struct cuts nothing
    text.remove(0, 4).unwrap();
    assert_eq!(text.to_string(), "ef");
    drop(limit);

    // the local timeline is full, the one of the other client has room
    let (doc, mut text) = two_clients();
    text.insert(4, "e").unwrap();
    pad(&doc, 2, 4);
    assert_eq!((blocks(&doc, 1), blocks(&doc, 2)), (1, 4));
    let _limit = ClientBlocks::set_limit(4);
    let before = doc.encode_update_v1().unwrap();
    refused(text.insert(2, "x"));
    refused(text.insert(0, "x"));
    assert_eq!(text.to_string(), "abcde");
    assert_eq!(doc.encode_update_v1().unwrap(), before);
    // the struct of the other client is not cut for an insert that found no
    // block
    assert_eq!((blocks(&doc, 1), blocks(&doc, 2)), (1, 4));
    // cuts of the other timeline need no local block
    text.remove(1, 2).unwrap();
    assert_eq!(text.to_string(), "ade");
    assert_eq!((blocks(&doc, 1), blocks(&doc, 2)), (3, 4));
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn a_remote_struct_that_finds_no_block_leaves_no_named_root() {
    let source = Doc::with_client(1);
    source.get_or_create_map("new").unwrap().insert("x".into(), 7).unwrap();
    let bytes = source.encode_update_v1().unwrap();
    let mut peer = Doc::with_client(2);
    let limit = ClientBlocks::set_limit(0);
    refused(peer.apply_update_from_binary_v1(&bytes));
    assert!(!peer.store.read().unwrap().types.contains_key("new"));
    assert_eq!(peer.get_state_vector().get(&1), 0);
    assert_eq!(blocks(&peer, 1), 0);
    drop(limit);
    peer.apply_update_from_binary_v1(bytes).unwrap();
    assert_eq!(
        serde_json::to_value(peer.get_map("new").unwrap()).unwrap(),
        serde_json::json!({"x":7})
    );
}

#[test]
fn a_remote_struct_cuts_its_origins_or_is_refused_whole() {
    // client 1 writes "abcd"; client 3 inserts "X" in the middle of it
    let source = Doc::with_client(1);
    let mut text = source.get_or_create_text("text").unwrap();
    text.insert(0, "abcd").unwrap();
    let base = source.encode_update_v1().unwrap();
    let mut other = Doc::with_client(3);
    other.apply_update_from_binary_v1(&base).unwrap();
    let state = other.get_state_vector();
    other.get_or_create_text("text").unwrap().insert(2, "X").unwrap();
    let insert = other.encode_state_as_update_v1(&state).unwrap();

    let mut peer = Doc::with_client(2);
    peer.apply_update_from_binary_v1(&base).unwrap();
    pad(&peer, 1, 3);
    let before = peer.encode_update_v1().unwrap();
    // the struct of client 1 is cut for the insert: its timeline is full
    let limit = ClientBlocks::set_limit(3);
    refused(peer.apply_update_from_binary_v1(&insert));
    assert_eq!(peer.get_or_create_text("text").unwrap().to_string(), "abcd");
    assert_eq!((blocks(&peer, 1), blocks(&peer, 3)), (3, 0));
    assert_eq!(peer.encode_update_v1().unwrap(), before);
    peer.store.read().unwrap().self_check().unwrap();
    drop(limit);
    let _limit = ClientBlocks::set_limit(4);
    peer.apply_update_from_binary_v1(&insert).unwrap();
    assert_eq!(peer.get_or_create_text("text").unwrap().to_string(), "abXcd");
    assert_eq!((blocks(&peer, 1), blocks(&peer, 3)), (4, 1));
}

#[test]
fn a_range_is_deleted_from_a_full_timeline_unless_it_cuts_a_struct() {
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    text.insert(0, "abcd").unwrap();
    doc.transact_mut(Origin::new("apart"), |tx| tx.text(&text)?.insert(4, "ef"))
        .unwrap();
    pad(&doc, 1, 4);
    let limit = ClientBlocks::set_limit(4);
    assert!(doc.store.read().unwrap().items[&1].is_full());
    let before = doc.encode_update_v1().unwrap();
    // one cut, and two
    refused(doc.transact_mut(None, |tx| tx.store_mut().delete_range(1, 0..2)));
    refused(doc.transact_mut(None, |tx| tx.store_mut().delete_range(1, 1..3)));
    assert_eq!(text.to_string(), "abcdef");
    assert_eq!(doc.encode_update_v1().unwrap(), before);
    // whole structs: no cut
    let whole = doc.store.read().unwrap().get_node(Id::new(1, 0)).unwrap().len();
    doc.transact_mut(None, |tx| tx.store_mut().delete_range(1, 0..whole))
        .unwrap();
    assert_eq!(text.to_string().len(), 6 - whole as usize);
    assert_eq!(blocks(&doc, 1), 4);
    drop(limit);
    // room for one cut only: a range that needs two is refused before the
    // first
    let _limit = ClientBlocks::set_limit(5);
    let tail = whole;
    let rest = doc.store.read().unwrap().get_node(Id::new(1, tail)).map(|n| n.len());
    if let Some(len) = rest.filter(|len| *len >= 3) {
        let before = doc.encode_update_v1().unwrap();
        refused(doc.transact_mut(None, |tx| tx.store_mut().delete_range(1, tail + 1..tail + len - 1)));
        assert_eq!(doc.encode_update_v1().unwrap(), before);
        assert_eq!(blocks(&doc, 1), 4);
    }
}

#[test]
fn undo_at_a_full_timeline_keeps_its_history_and_fits_exactly() {
    let doc = Doc::with_client(1);
    let mut map = doc.get_or_create_map("map").unwrap();
    map.insert("key".into(), 7).unwrap();
    let undo: UndoManager<u64> = UndoManager::new(&doc, [(&map).into()], UndoOptions::default()).unwrap();
    map.remove("key");
    pad(&doc, 1, 4);
    let top = undo.peek(UndoStack::Undo).unwrap();
    let before = doc.encode_update_v1().unwrap();

    // the value comes back as a new item: one block
    let limit = ClientBlocks::set_limit(4);
    refused(undo.undo());
    assert_eq!(doc.encode_update_v1().unwrap(), before);
    assert_eq!(undo.peek(UndoStack::Undo).as_ref(), Some(&top));
    assert!(!undo.can_redo());
    assert!(!map.contains_key("key"));
    doc.store.read().unwrap().self_check().unwrap();
    drop(limit);

    let limit = ClientBlocks::set_limit(5);
    assert_eq!(undo.undo().unwrap(), Some(top));
    assert_eq!(serde_json::to_value(&map).unwrap(), serde_json::json!({"key":7}));
    assert_eq!(blocks(&doc, 1), 5);
    assert!(undo.can_redo());
    // the redo deletes the value again: no block
    assert!(undo.redo().unwrap().is_some());
    assert!(!map.contains_key("key"));
    assert_eq!(blocks(&doc, 1), 5);
    // and the undo of that finds the timeline full
    let top = undo.peek(UndoStack::Undo).unwrap();
    refused(undo.undo());
    assert_eq!(undo.peek(UndoStack::Undo).as_ref(), Some(&top));
    assert!(undo.can_redo() || undo.peek(UndoStack::Redo).is_none());
    drop(limit);
}

#[test]
fn undo_of_an_insert_adds_no_block_to_a_full_timeline() {
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    let undo: UndoManager<u64> = UndoManager::new(&doc, [(&text).into()], UndoOptions::default()).unwrap();
    text.insert(0, "abc").unwrap();
    pad(&doc, 1, 3);
    let limit = ClientBlocks::set_limit(3);
    assert!(undo.undo().unwrap().is_some());
    assert_eq!(text.to_string(), "");
    assert_eq!(blocks(&doc, 1), 3);
    // the redo writes the text again: a block the timeline has not
    let top = undo.peek(UndoStack::Redo).unwrap();
    let before = doc.encode_update_v1().unwrap();
    refused(undo.redo());
    assert_eq!(doc.encode_update_v1().unwrap(), before);
    assert_eq!(undo.peek(UndoStack::Redo).as_ref(), Some(&top));
    assert_eq!(text.to_string(), "");
    drop(limit);
    let _limit = ClientBlocks::set_limit(4);
    assert!(undo.redo().unwrap().is_some());
    assert_eq!(text.to_string(), "abc");
    assert_eq!(blocks(&doc, 1), 4);
}

fn snap(store: &DocStore) -> Vec<String> {
    let mut clients: Vec<_> = store.items.keys().copied().collect();
    clients.sort_unstable();
    let mut out = Vec::new();
    for client in clients {
        for node in store.items[&client].nodes(client) {
            let item = node
                .as_item()
                .map(|i| {
                    let item = store.type_arena.items.get(i).expect("live item");
                    format!(
                        "{:?} {} {:?} {:?} {:?} {:?} {:?}",
                        item.id,
                        item.len,
                        item.content,
                        item.left,
                        item.right,
                        item.origin_left_id(),
                        item.origin_right_id()
                    )
                })
                .unwrap_or_default();
            out.push(format!("{:?} {} {:?} | {item}", node.id, node.len, node.kind));
        }
        out.push(format!("end {}", store.items[&client].end_clock()));
    }
    out
}

#[test]
fn split_node_refuses_before_it_changes_anything() {
    let mut store = DocStore::with_client(1);
    let id = Id::new(1, 0);
    let item = ItemBuilder::new()
        .id(id)
        .content(Content::String("abcdef".into()))
        .build();
    let node = Node::store_item(&mut store.type_arena, item);
    store.add_node(node).unwrap();
    let before = snap(&store);
    assert_eq!(before.len(), 2);

    // at or outside the ends of the block, from its start and from inside it
    for (at, diff) in [
        (0u64, 0u64),
        (0, 6),
        (0, 7),
        (0, u64::MAX),
        (3, 0),
        (3, 6),
        (5, u64::MAX),
    ] {
        assert_eq!(
            store.split_node(Id::new(1, at), diff).err(),
            Some(JwstCodecError::ItemSplitNotSupport),
            "{at} {diff}"
        );
        assert_eq!(snap(&store), before, "{at} {diff}");
    }
    // no such client, no such clock
    assert_eq!(
        store.split_node(Id::new(9, 0), 1).err(),
        Some(JwstCodecError::StructSequenceNotExists(9))
    );
    assert_eq!(
        store.split_node(Id::new(1, 6), 1).err(),
        Some(JwstCodecError::StructSequenceNotExists(1))
    );
    assert_eq!(snap(&store), before);
    // no room for the right half: in the arena, and on the timeline
    store.type_arena.items.set_limit(1);
    assert!(store.split_node(id, 3).is_err());
    assert_eq!(snap(&store), before);
    store.type_arena.items.set_limit(u32::MAX as usize);
    {
        let _limit = ClientBlocks::set_limit(1);
        refused(store.split_node(id, 3));
        assert_eq!(snap(&store), before);
    }

    // a block that is no item
    store.add_node(Node::new_gc(Id::new(1, 6), 4)).unwrap();
    let before = snap(&store);
    assert_eq!(
        store.split_node(Id::new(1, 7), 1).err(),
        Some(JwstCodecError::ItemSplitNotSupport)
    );
    assert_eq!(snap(&store), before);

    // and the split itself, by an id inside the block
    let (left, right) = store.split_node(Id::new(1, 2), 3).unwrap();
    assert_eq!((left.id, left.len, right.id, right.len), (id, 3, Id::new(1, 3), 3));
    let (left, right) = store.split_node(Id::new(1, 4), 1).unwrap();
    assert_eq!(
        (left.id, left.len, right.id, right.len),
        (Id::new(1, 3), 1, Id::new(1, 4), 2)
    );
    let nodes: Vec<_> = store.items[&1].nodes(1).map(|n| (n.clock(), n.len())).collect();
    assert_eq!(nodes, [(0, 3), (3, 1), (4, 2), (6, 4)]);
    assert_eq!(store.items[&1].end_clock(), 10);
}

#[test]
fn check_append_refuses_what_append_refuses() {
    let mut timeline = ClientBlocks::default();
    let block = |clock, kind| BlockRef { clock, kind };
    for (clock, len) in [
        (5u64, 0u64),
        (5, 3),
        (8, 0),
        (9, 1),
        (7, 1),
        (8, u64::MAX),
        (8, u64::MAX - 8),
        (u64::MAX, 1),
    ] {
        let asked = timeline.check_append(clock, len);
        let mut copy = ClientBlocks::default();
        for node in timeline.nodes(1) {
            copy.append(block(node.clock(), node.kind), node.len()).unwrap();
        }
        let done = timeline.append(block(clock, BlockKind::Gc), len);
        assert_eq!(asked, done, "{clock} {len}");
        if done.is_err() {
            assert_eq!(
                timeline.nodes(1).map(|n| (n.clock(), n.len())).collect::<Vec<_>>(),
                copy.nodes(1).map(|n| (n.clock(), n.len())).collect::<Vec<_>>()
            );
            assert_eq!(timeline.end_clock(), copy.end_clock());
        }
    }
    assert_eq!(timeline.len(), 2);
    assert_eq!(timeline.end_clock(), u64::MAX);
    // a full timeline refuses a block it would take otherwise, both ways
    let _limit = ClientBlocks::set_limit(2);
    let mut full = ClientBlocks::default();
    full.append(block(0, BlockKind::Gc), 1).unwrap();
    full.append(block(1, BlockKind::Gc), 1).unwrap();
    assert_eq!(full.check_append(2, 1), full.append(block(2, BlockKind::Gc), 1));
    assert!(full.check_append(2, 1).is_err());
    assert_eq!(full.len(), 2);
}
