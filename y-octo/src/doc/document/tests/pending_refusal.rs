//! What the document keeps waiting ([Doc::has_pending_updates]) is not lost
//! when it refuses a struct or a deletion: one refused for room waits with
//! the rest and goes in once there is room, one refused for what it is goes
//! alone.

use super::*;

/// What `edit` adds to `author`, as the update of that edit alone (with
/// every deletion of the author so far).
fn edit(author: &Doc, edit: impl FnOnce(&Doc)) -> Vec<u8> {
    let before = author.get_state_vector();
    edit(author);
    author.encode_state_as_update_v1(&before).unwrap()
}

fn give(to: &Doc, update: &[u8]) -> JwstCodecResult {
    to.apply_update_with_origin(Update::decode_v1(update).unwrap(), None)
}

/// A replica that has seen `updates`.
fn replica(client: Client, updates: &[&[u8]]) -> Doc {
    let doc = Doc::with_client(client);
    for update in updates {
        give(&doc, update).unwrap();
    }
    doc
}

fn insert(doc: &Doc, root: &str, at: u64, value: &str) {
    doc.get_or_create_text(root).unwrap().insert(at, value).unwrap();
}

fn text(doc: &Doc, root: &str) -> String {
    doc.get_or_create_text(root).unwrap().to_string()
}

fn refusal(message: &str) -> JwstCodecResult {
    Err(JwstCodecError::IncompleteDocument(message.into()))
}

/// The two documents hold the same structs and deletions, keep the same
/// waiting, and are sound.
fn assert_same(doc: &Doc, control: &Doc) {
    doc.store.read().unwrap().self_check().unwrap();
    assert_eq!(doc.get_state_vector(), control.get_state_vector());
    assert_eq!(doc.has_pending_updates(), control.has_pending_updates());
    assert_eq!(doc.encode_update_v1().unwrap(), control.encode_update_v1().unwrap());
}

/// Makes the store of `doc` take what a new one takes.
fn lift(doc: &Doc) {
    let mut store = doc.store.write().unwrap();
    store.scan_limit = None;
    store.type_arena.set_limit(None);
    store.type_arena.items.set_limit(u32::MAX as usize);
}

/// Two replicas type after the same `a` of the text `t` without seeing each
/// other: `b` by client 20, and what the client `late` types by `typing`,
/// one update an edit. A replica that holds `a` and `b` walks `b` in the
/// conflict scan of each struct of `late` that follows `a`.
struct Race {
    /// `a` alone
    a: Vec<u8>,
    /// `a` and `b`
    history: Vec<u8>,
    /// the edits of `late`
    late: Vec<Vec<u8>>,
}

fn race(late: Client, typing: &[(u64, &str)]) -> Race {
    let a = edit(&Doc::with_client(10), |doc| insert(doc, "t", 0, "a"));
    let second = replica(20, &[&a]);
    insert(&second, "t", 1, "b");
    let third = replica(late, &[&a]);
    Race {
        history: second.encode_update_v1().unwrap(),
        late: typing
            .iter()
            .map(|(at, value)| edit(&third, |doc| insert(doc, "t", *at, value)))
            .collect(),
        a,
    }
}

/// `z` after an `a` of the text `q`, by the client `author`: it waits for
/// `first`, the `a`, and has nothing to do with the text `t`.
struct Unrelated {
    first: Vec<u8>,
    z: Vec<u8>,
}

fn unrelated(author: Client) -> Unrelated {
    let first = edit(&Doc::with_client(50), |doc| insert(doc, "q", 0, "a"));
    let z = edit(&replica(author, &[&first]), |doc| insert(doc, "q", 1, "z"));
    Unrelated { first, z }
}

#[test]
fn a_struct_refused_for_room_when_it_is_retried_keeps_waiting() {
    let race = race(30, &[(1, "x")]);
    let doc = Doc::with_client(1);
    let control = Doc::with_client(1);
    for doc in [&doc, &control] {
        give(doc, &race.late[0]).unwrap();
        assert!(doc.has_pending_updates());
    }

    // `a` and `b` go in; `x`, tried again, finds `b` in its way and a scan
    // that takes no candidate
    doc.store.write().unwrap().scan_limit = Some(0);
    assert_eq!(give(&doc, &race.history), refusal(TOO_MANY_CANDIDATES));
    assert_eq!(text(&doc, "t"), "ab");
    assert!(doc.has_pending_updates(), "the struct that waited is still there");
    // as long as there is no room it is refused again, and waits on
    assert_eq!(give(&doc, &race.history), refusal(TOO_MANY_CANDIDATES));
    assert!(doc.has_pending_updates());

    // with room, the update that was refused is all it takes
    lift(&doc);
    give(&doc, &race.history).unwrap();
    give(&control, &race.history).unwrap();
    assert_eq!(text(&doc, "t"), "abx");
    assert!(!doc.has_pending_updates());
    assert_same(&doc, &control);
}

#[test]
fn a_refused_struct_takes_no_unrelated_waiting_struct_with_it() {
    // the unrelated struct is walked before the refused one (40) or is
    // still on its queue when that one is refused (25)
    for author in [25, 40] {
        let race = race(30, &[(1, "x")]);
        let other = unrelated(author);
        let doc = Doc::with_client(1);
        let control = Doc::with_client(1);
        for doc in [&doc, &control] {
            give(doc, &other.z).unwrap();
            give(doc, &race.late[0]).unwrap();
        }

        doc.store.write().unwrap().scan_limit = Some(0);
        assert_eq!(give(&doc, &race.history), refusal(TOO_MANY_CANDIDATES));
        lift(&doc);
        give(&doc, &race.history).unwrap();
        give(&control, &race.history).unwrap();
        assert_eq!(text(&doc, "t"), "abx");
        assert!(doc.has_pending_updates(), "`z` waits for its own text");
        assert_same(&doc, &control);

        for doc in [&doc, &control] {
            give(doc, &other.first).unwrap();
            assert_eq!(text(doc, "q"), "az");
            assert!(!doc.has_pending_updates());
        }
        assert_same(&doc, &control);
    }
}

#[test]
fn the_structs_that_wait_for_a_refused_one_wait_with_it_in_their_order() {
    // `x` and then `w` by one client, and `y` by another one that saw both:
    // the walk reaches `x` from `y`, and `w` is behind `x` on its queue
    let race = race(30, &[(1, "x"), (2, "w")]);
    let fourth = replica(40, &[&race.a, &race.late[0], &race.late[1]]);
    let y = edit(&fourth, |doc| insert(doc, "t", 3, "y"));

    let doc = Doc::with_client(1);
    let control = Doc::with_client(1);
    for doc in [&doc, &control] {
        for update in [&y, &race.late[1], &race.late[0]] {
            give(doc, update).unwrap();
        }
    }
    doc.store.write().unwrap().scan_limit = Some(0);
    for _ in 0..2 {
        assert_eq!(give(&doc, &race.history), refusal(TOO_MANY_CANDIDATES));
        assert!(doc.has_pending_updates());
    }
    lift(&doc);
    give(&doc, &race.history).unwrap();
    give(&control, &race.history).unwrap();
    assert_eq!(text(&doc, "t"), "abxwy");
    assert!(!doc.has_pending_updates());
    assert_same(&doc, &control);
}

#[test]
fn a_refused_part_of_an_update_leaves_what_waited_as_it_was() {
    let other = unrelated(40);
    let doc = replica(1, &[&other.z]);
    let control = replica(1, &[&other.z]);
    let waiting = doc.store.read().unwrap().pending.as_ref().unwrap().encode_v1().unwrap();

    // a text nested in a map, for a document that takes no type
    let nested = edit(&Doc::with_client(60), |doc| {
        let child = doc.create_text().unwrap();
        doc.get_or_create_map("m").unwrap().insert("k".into(), child).unwrap();
    });
    doc.store.write().unwrap().type_arena.set_limit(Some(0));
    assert_eq!(give(&doc, &nested), refusal(TOO_MANY_TYPES));
    assert_eq!(
        doc.store.read().unwrap().pending.as_ref().unwrap().encode_v1().unwrap(),
        waiting
    );

    lift(&doc);
    for doc in [&doc, &control] {
        give(doc, &nested).unwrap();
        give(doc, &other.first).unwrap();
        assert_eq!(text(doc, "q"), "az");
    }
    assert_same(&doc, &control);
}

/// The store of `doc` takes `spare` more items than it holds.
fn spare_items(doc: &Doc, spare: usize) {
    let mut store = doc.store.write().unwrap();
    let limit = store.type_arena.items.occupied() + spare;
    store.type_arena.items.set_limit(limit);
}

#[test]
#[allow(clippy::single_range_in_vec_init)]
fn a_deletion_refused_for_room_keeps_waiting_with_the_part_past_the_clocks() {
    // `abcd`, then `efgh` after it, then `cdef` deleted: three updates of
    // one client, the last one deletions only
    let author = Doc::with_client(10);
    let head = edit(&author, |doc| insert(doc, "t", 0, "abcd"));
    let tail = edit(&author, |doc| insert(doc, "t", 4, "efgh"));
    let cut = edit(&author, |doc| {
        doc.get_or_create_text("t").unwrap().remove(2, 4).unwrap();
    });

    // the cut of `abcd` at `c` finds no item, or no block on the timeline
    for blocks in [false, true] {
        let other = unrelated(40);
        let doc = Doc::with_client(1);
        let control = Doc::with_client(1);
        for doc in [&doc, &control] {
            give(doc, &cut).unwrap();
            give(doc, &other.z).unwrap();
            assert_eq!(doc.get_state_vector(), StateVector::default());
        }

        // `abcd` goes in; of the deletion that waited, `cd` is there to
        // delete and `ef` waits on
        if blocks {
            let _limit = ClientBlocks::set_limit(1);
            assert_eq!(give(&doc, &head), refusal(TOO_MANY_STRUCTS));
        } else {
            spare_items(&doc, 1);
            assert_eq!(give(&doc, &head), refusal(TOO_MANY_ITEMS));
        }
        assert_eq!(text(&doc, "t"), "abcd");
        {
            let store = doc.store.read().unwrap();
            let waiting = store.pending.as_ref().expect("the deletion and `z` wait");
            assert_eq!(waiting.delete_set.clients[&10].canonical_ranges(), [2..6]);
            assert!(waiting.structs.contains_key(&40));
        }

        lift(&doc);
        give(&control, &head).unwrap();
        assert_eq!(text(&control, "t"), "ab");
        for doc in [&doc, &control] {
            give(doc, &tail).unwrap();
            assert_eq!(text(doc, "t"), "abgh");
            assert!(doc.has_pending_updates(), "`z` waits for its own text");
        }
        assert_same(&doc, &control);
        for doc in [&doc, &control] {
            give(doc, &other.first).unwrap();
            assert_eq!(text(doc, "q"), "az");
            assert!(!doc.has_pending_updates());
        }
        assert_same(&doc, &control);
    }
}

#[test]
fn a_deletion_refused_for_room_after_its_struct_was_retried_keeps_waiting() {
    // `uvwxyz` after an `a` it waits for, then `v` and `xy` of it deleted
    let a = edit(&Doc::with_client(10), |doc| insert(doc, "t", 0, "a"));
    let second = replica(30, &[&a]);
    let typed = edit(&second, |doc| insert(doc, "t", 1, "uvwxyz"));
    let cut = edit(&second, |doc| {
        let mut text = doc.get_or_create_text("t").unwrap();
        text.remove(2, 1).unwrap();
        text.remove(3, 2).unwrap();
    });

    let doc = Doc::with_client(1);
    let control = Doc::with_client(1);
    for doc in [&doc, &control] {
        give(doc, &typed).unwrap();
        give(doc, &cut).unwrap();
    }
    // room for `a`, for `uvwxyz` and for the two cuts around `v`: the
    // deletion of `xy` finds one item for its two cuts
    spare_items(&doc, 5);
    assert_eq!(give(&doc, &a), refusal(TOO_MANY_ITEMS));
    assert_eq!(text(&doc, "t"), "auwxyz");
    assert!(doc.has_pending_updates(), "the deletion of `xy` waits");

    lift(&doc);
    give(&doc, &a).unwrap();
    give(&control, &a).unwrap();
    assert_eq!(text(&doc, "t"), "auwz");
    assert!(!doc.has_pending_updates());
    assert_same(&doc, &control);
}

#[test]
fn a_struct_refused_by_a_timeline_with_one_block_to_spare_keeps_waiting() {
    // `abcd`, then `x` in the middle of it by the same client: `x` takes a
    // block of the timeline `abcd` is on and cuts `abcd` in two
    let author = Doc::with_client(10);
    let abcd = edit(&author, |doc| insert(doc, "t", 0, "abcd"));
    let x = edit(&author, |doc| insert(doc, "t", 2, "x"));

    let doc = Doc::with_client(1);
    let control = Doc::with_client(1);
    for doc in [&doc, &control] {
        give(doc, &x).unwrap();
        assert!(doc.has_pending_updates());
    }
    // the timeline takes the block of `abcd` and one more: not the two
    // blocks of `x`, and nothing is cut
    {
        let _limit = ClientBlocks::set_limit(2);
        assert_eq!(give(&doc, &abcd), refusal(TOO_MANY_STRUCTS));
    }
    assert_eq!(text(&doc, "t"), "abcd");
    assert_eq!(doc.store.read().unwrap().items[&10].len(), 1);
    assert!(doc.has_pending_updates());

    give(&doc, &abcd).unwrap();
    give(&control, &abcd).unwrap();
    assert_eq!(text(&doc, "t"), "abxcd");
    assert!(!doc.has_pending_updates());
    assert_same(&doc, &control);
}

#[test]
fn a_struct_that_names_a_root_and_carries_a_type_keeps_waiting_when_one_type_fits() {
    // an `a` in the text `t`, then a text under a key of the map `m`: the
    // second struct is the first to name `m` and carries a type of its own
    let author = Doc::with_client(30);
    let first = edit(&author, |doc| insert(doc, "t", 0, "a"));
    let nested = edit(&author, |doc| {
        let child = doc.create_text().unwrap();
        doc.get_or_create_map("m").unwrap().insert("k".into(), child).unwrap();
    });

    let doc = Doc::with_client(1);
    let control = Doc::with_client(1);
    for doc in [&doc, &control] {
        give(doc, &nested).unwrap();
        assert!(doc.has_pending_updates());
    }
    // `t` and one more type fit: not the two of the struct that waited
    doc.store.write().unwrap().type_arena.set_limit(Some(2));
    assert_eq!(give(&doc, &first), refusal(TOO_MANY_TYPES));
    assert_eq!(text(&doc, "t"), "a");
    assert_eq!(doc.store.read().unwrap().type_arena.len(), 1);
    assert!(doc.has_pending_updates());

    lift(&doc);
    give(&doc, &first).unwrap();
    give(&control, &first).unwrap();
    assert!(doc.get_or_create_map("m").unwrap().get("k").is_some());
    assert!(!doc.has_pending_updates());
    assert_same(&doc, &control);
}

/// A struct of the client `author` that follows the `a` of the text `t`
/// (client 10) and names the text `elsewhere` as its parent: the document
/// refuses it once it holds `a`, whenever it is tried.
fn misplaced(author: Client, clock: Clock, len: u64) -> WireStruct {
    WireStruct::Item(Box::new(WireItem {
        id: Id::new(author, clock),
        len,
        origin_left_id: Some(Id::new(10, 0)),
        origin_right_id: None,
        parent: Some(WireParent::Root("elsewhere".into())),
        parent_sub: None,
        flags: item_flags::ITEM_COUNTABLE,
        content: WireContent::String("!".repeat(len as usize)),
    }))
}

fn update_of(structs: impl IntoIterator<Item = WireStruct>) -> Update {
    let mut update = Update::default();
    for wire in structs {
        update.structs.entry(wire.client()).or_default().push_back(wire);
    }
    update
}

#[test]
fn a_struct_refused_for_what_it_is_goes_alone_and_is_not_tried_again() {
    // the unrelated struct is walked before the refused one (40) or is
    // still on its queue when that one is refused (25)
    for author in [25, 40] {
        let race = race(60, &[(1, "x")]);
        let other = unrelated(author);
        let doc = Doc::with_client(1);
        // the control is never sent the struct
        let control = Doc::with_client(1);
        give(&control, &other.z).unwrap();
        give(&doc, &other.z).unwrap();
        doc.apply_update_with_origin(update_of([misplaced(30, 0, 1)]), None)
            .unwrap();

        // `a` arrives: the struct that waited for it is refused, once
        assert_eq!(give(&doc, &race.a), Err(JwstCodecError::InvalidParent));
        give(&control, &race.a).unwrap();
        assert_eq!(text(&doc, "t"), "a");
        assert_same(&doc, &control);

        // every later update is taken
        for update in [&race.history, &race.late[0]] {
            give(&doc, update).unwrap();
            give(&control, update).unwrap();
        }
        assert_eq!(text(&doc, "t"), "abx");
        assert!(doc.has_pending_updates(), "`z` waits for its own text");
        assert_same(&doc, &control);
        for doc in [&doc, &control] {
            give(doc, &other.first).unwrap();
            assert_eq!(text(doc, "q"), "az");
            assert!(!doc.has_pending_updates());
        }
        assert_same(&doc, &control);
    }
}

#[test]
fn what_follows_a_struct_refused_for_what_it_is_waits_and_blocks_nothing() {
    let race = race(60, &[(1, "x")]);
    let doc = Doc::with_client(1);
    // The document will refuse the first struct of the client 30. Two
    // follow it: the next one of that client, behind it on its queue, and
    // one of the client 40, which the walk takes off its queue first and
    // holds while it turns to what that one asks for.
    let follower = |author, clock| {
        let mut wire = misplaced(author, clock, 1);
        if let WireStruct::Item(item) = &mut wire {
            item.origin_left_id = Some(Id::new(30, 0));
            item.parent = None;
        }
        wire
    };
    doc.apply_update_with_origin(update_of([misplaced(30, 0, 1), follower(30, 1), follower(40, 0)]), None)
        .unwrap();

    assert_eq!(give(&doc, &race.a), Err(JwstCodecError::InvalidParent));
    // both wait for a clock that will not come, and are in nobody's way
    for update in [&race.history, &race.late[0], &race.history] {
        give(&doc, update).unwrap();
        let store = doc.store.read().unwrap();
        let waiting = store.pending.as_ref().expect("the two that follow");
        assert_eq!(waiting.structs[&30].len(), 1);
        assert_eq!(waiting.structs[&30][0].clock(), 1);
        assert_eq!(waiting.structs[&40].len(), 1);
    }
    assert_eq!(text(&doc, "t"), "abx");
    assert_eq!(doc.get_state_vector().get(&30), 0);
    assert_eq!(doc.get_state_vector().get(&40), 0);
    doc.store.read().unwrap().self_check().unwrap();
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// Updates of four replicas that edit a text, a map and a list and see each
/// other now and then. An update is what one edit added, or everything its
/// author got since an earlier edit: a struct comes whole, in parts and
/// twice, and every update carries all the deletions its author knows.
fn history(rng: &mut Rng, edits: usize) -> Vec<Vec<u8>> {
    let docs: Vec<Doc> = [11, 12, 13, 14].into_iter().map(Doc::with_client).collect();
    let mut marks = vec![vec![StateVector::default()]; docs.len()];
    let mut updates = Vec::new();
    while updates.len() < edits {
        let at = rng.below(4) as usize;
        let doc = &docs[at];
        if rng.below(4) == 0 {
            let from = &docs[(at + 1 + rng.below(3) as usize) % 4];
            let seen = from.encode_state_as_update_v1(&doc.get_state_vector()).unwrap();
            give(doc, &seen).unwrap();
            continue;
        }
        let before = doc.get_state_vector();
        match rng.below(9) {
            0..=2 => {
                let mut text = doc.get_or_create_text("text").unwrap();
                let at = rng.below(text.len() + 1);
                text.insert(at, ["a", "bc", "def"][rng.below(3) as usize]).unwrap();
            }
            3 | 4 => {
                let mut text = doc.get_or_create_text("text").unwrap();
                if !text.is_empty() {
                    let at = rng.below(text.len());
                    let len = 1 + rng.below((text.len() - at).min(4));
                    text.remove(at, len).unwrap();
                }
            }
            5 | 6 => {
                let mut map = doc.get_or_create_map("map").unwrap();
                let key = format!("k{}", rng.below(3));
                if rng.below(3) == 0 {
                    map.remove(&key);
                } else {
                    map.insert(key, rng.below(100) as i32).unwrap();
                }
            }
            _ => {
                let mut list = doc.get_or_create_array("list").unwrap();
                let at = rng.below(list.len() + 1);
                if rng.below(2) == 0 {
                    list.insert(at, doc.create_map().unwrap()).unwrap();
                } else {
                    list.insert(at, rng.below(100) as i32).unwrap();
                }
            }
        }
        let marks = &mut marks[at];
        let since = if rng.below(3) == 0 {
            marks[rng.below(marks.len() as u64) as usize].clone()
        } else {
            before.clone()
        };
        updates.push(doc.encode_state_as_update_v1(&since).unwrap());
        marks.push(before);
    }
    updates
}

/// What the store refuses a delivery for.
#[derive(Clone, Copy, Debug)]
enum Short {
    /// the conflict scans take this many candidates
    Candidates(usize),
    /// the arenas and the longest timeline take this many more than they
    /// hold
    Types(usize),
    Items(usize),
    Blocks(usize),
}

/// Gives `update` to `doc` while its store is short of something, and lets
/// it have room again.
fn give_short(doc: &Doc, update: &[u8], short: Short) -> JwstCodecResult {
    let mut blocks = None;
    {
        let mut store = doc.store.write().unwrap();
        match short {
            Short::Candidates(limit) => store.scan_limit = Some(limit),
            Short::Types(spare) => {
                let limit = store.type_arena.len() + spare;
                store.type_arena.set_limit(Some(limit));
            }
            Short::Items(spare) => {
                let limit = store.type_arena.items.occupied() + spare;
                store.type_arena.items.set_limit(limit);
            }
            Short::Blocks(spare) => {
                let longest = store.items.values().map(ClientBlocks::len).max().unwrap_or(0);
                blocks = Some(ClientBlocks::set_limit(longest + spare));
            }
        }
    }
    let result = give(doc, update);
    drop(blocks);
    lift(doc);
    result
}

/// One history, given in a random order to a replica that is short of room
/// now and then and to one that never is. Returns how many deliveries the
/// first one refused, and how many of them with something waiting.
fn deliver_with_refusals(seed: u64, edits: usize) -> (usize, usize) {
    let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
    let updates = history(&mut rng, edits);

    let mut order: Vec<usize> = (0..updates.len()).collect();
    for i in (1..order.len()).rev() {
        order.swap(i, rng.below(i as u64 + 1) as usize);
    }
    for _ in 0..updates.len() / 8 {
        let at = rng.below(order.len() as u64 + 1) as usize;
        order.insert(at, rng.below(updates.len() as u64) as usize);
    }

    let doc = Doc::with_client(1);
    let control = Doc::with_client(1);
    // the deliveries the store is short for, and the updates it refused
    let mut short: Option<(Short, u64)> = None;
    let mut refused: Vec<usize> = Vec::new();
    let (mut refusals, mut with_waiting) = (0, 0);
    for index in order {
        if short.is_none() && rng.below(3) == 0 {
            let kind = match rng.below(4) {
                0 => Short::Candidates(rng.below(3) as usize),
                1 => Short::Types(rng.below(2) as usize),
                2 => Short::Items(rng.below(4) as usize),
                _ => Short::Blocks(rng.below(3) as usize),
            };
            short = Some((kind, 1 + rng.below(3)));
        }
        let waited = doc.has_pending_updates();
        let result = match short {
            Some((kind, _)) => give_short(&doc, &updates[index], kind),
            None => give(&doc, &updates[index]),
        };
        if let Err(error) = result {
            assert!(refused_for_room(&error), "seed {seed}: {error}");
            refused.push(index);
            refusals += 1;
            with_waiting += usize::from(waited);
        }
        doc.store.read().unwrap().self_check().unwrap();
        give(&control, &updates[index]).unwrap();

        if let Some((_, left)) = &mut short {
            *left -= 1;
            if *left == 0 {
                short = None;
                // with room again, the refused updates are all it takes
                for index in refused.drain(..) {
                    give(&doc, &updates[index]).unwrap();
                    give(&control, &updates[index]).unwrap();
                }
            }
        }
    }
    for index in refused {
        give(&doc, &updates[index]).unwrap();
        give(&control, &updates[index]).unwrap();
    }

    assert!(!control.has_pending_updates(), "seed {seed}");
    assert!(!doc.has_pending_updates(), "seed {seed}");
    doc.store.read().unwrap().self_check().unwrap();
    assert_eq!(doc.get_state_vector(), control.get_state_vector(), "seed {seed}");
    assert_eq!(
        doc.encode_update_v1().unwrap(),
        control.encode_update_v1().unwrap(),
        "seed {seed}"
    );
    (refusals, with_waiting)
}

#[test]
fn random_refusals_for_room_lose_nothing() {
    // Miri runs a few short histories
    let (seeds, edits) = if cfg!(miri) { (3, 24) } else { (300, 64) };
    let (mut refusals, mut with_waiting) = (0, 0);
    for seed in 0..seeds {
        let (refused, waiting) = deliver_with_refusals(seed, edits);
        refusals += refused;
        with_waiting += waiting;
    }
    // the histories do reach the refusals this is about
    assert!(
        refusals >= seeds as usize && with_waiting >= seeds as usize / 2,
        "{refusals} refusals, {with_waiting} with something waiting"
    );
}
