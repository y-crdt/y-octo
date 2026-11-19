//! Regressions for malformed or hostile remote input: each update below is
//! hand-encoded so it reaches a path honest Yjs peers never produce.

use super::*;

const STRING: u8 = 4;
const FORMAT: u8 = 6;
const TYPE: u8 = 7;
const ANY: u8 = 8;
const DOC: u8 = 9;
const HAS_LEFT: u8 = item_flags::ITEM_HAS_LEFT_ID;
const HAS_RIGHT: u8 = item_flags::ITEM_HAS_RIGHT_ID;
const HAS_SUB: u8 = item_flags::ITEM_HAS_PARENT_SUB;
const KIND_MAP: u64 = 1;

/// Minimal Update V1 writer.
#[derive(Default)]
struct Wire(RawEncoder);

impl Wire {
    fn u(mut self, value: u64) -> Self {
        self.0.write_var_u64(value).unwrap();
        self
    }

    fn s(mut self, value: &str) -> Self {
        self.0.write_var_string(value).unwrap();
        self
    }

    fn b(mut self, value: u8) -> Self {
        self.0.write_u8(value).unwrap();
        self
    }

    fn raw(mut self, bytes: &[u8]) -> Self {
        for byte in bytes {
            self.0.write_u8(*byte).unwrap();
        }
        self
    }

    fn bytes(self) -> Vec<u8> {
        self.0.into_inner()
    }
}

/// One update: `blocks` are `(client, clock, structs)` and there are no
/// deletions.
fn update(blocks: &[(u64, u64, Vec<Vec<u8>>)]) -> Vec<u8> {
    let mut wire = Wire::default().u(blocks.len() as u64);
    for (client, clock, structs) in blocks {
        wire = wire.u(structs.len() as u64).u(*client).u(*clock);
        for item in structs {
            wire = wire.raw(item);
        }
    }
    wire.u(0).bytes()
}

fn in_root(tag: u8, root: &str, sub: Option<&str>) -> Wire {
    let wire = Wire::default()
        .b(tag | if sub.is_some() { HAS_SUB } else { 0 })
        .u(1)
        .s(root);
    match sub {
        Some(sub) => wire.s(sub),
        None => wire,
    }
}

fn in_item(tag: u8, parent: Id, sub: &str) -> Wire {
    Wire::default()
        .b(tag | HAS_SUB)
        .u(0)
        .u(parent.client)
        .u(parent.clock)
        .s(sub)
}

// The integrated prefix of an overlapping item became its left neighbor
// unchecked. Here the prefix is the carrier of the map the remainder claims
// as its parent: replacing the "previous value" deleted the carrier while
// its type was mutably borrowed as the parent (aliasing `&mut YType`).
#[test]
fn overlapping_item_cannot_adopt_its_parent_carrier() {
    let mut doc = Doc::with_client(1);
    let carrier = in_root(TYPE, "root", Some("k")).u(KIND_MAP).bytes();
    doc.apply_update_from_binary_v1(update(&[(5, 0, vec![carrier])]))
        .unwrap();

    // a same-client parent cannot precede its child, so the remainder is
    // kept as a GC range
    let overlapping = in_item(STRING, Id::new(5, 0), "k").s("ab").bytes();
    doc.apply_update_from_binary_v1(update(&[(5, 0, vec![overlapping])]))
        .unwrap();
    assert_eq!(doc.get_state_vector(), StateVector::from([(5, 2)]));
    assert!(doc.store.read().unwrap().get_node(Id::new(5, 1)).unwrap().is_gc());
    let root = doc.get_or_create_map("root").unwrap();
    let Some(Value::Map(map)) = root.get("k") else {
        panic!("the carrier stays the map value");
    };
    assert!(map.is_empty());
}

// The same overlap across clients would splice an array's list into a
// map entry's list.
#[test]
fn overlapping_item_cannot_splice_containers() {
    let mut doc = Doc::with_client(1);
    let carrier = in_root(TYPE, "root", Some("m")).u(KIND_MAP).bytes();
    let element = in_root(ANY, "list", None).u(1).b(125).u(7).bytes();
    doc.apply_update_from_binary_v1(update(&[(1, 0, vec![carrier]), (2, 0, vec![element])]))
        .unwrap();

    let overlapping = in_item(STRING, Id::new(1, 0), "k").s("xy").bytes();
    assert_eq!(
        doc.apply_update_from_binary_v1(update(&[(2, 0, vec![overlapping])])),
        Err(JwstCodecError::InvalidParent)
    );

    let list = doc.get_or_create_array("list").unwrap();
    assert_eq!(list.iter().collect::<Vec<_>>(), vec![Value::Any(Any::Integer(7))]);
    let Some(Value::Map(map)) = doc.get_or_create_map("root").unwrap().get("m") else {
        panic!("map carrier survives");
    };
    assert!(map.is_empty());
}

// Origins resolving into two different lists.
#[test]
fn origins_must_share_a_container() {
    let mut doc = Doc::with_client(1);
    let a = in_root(STRING, "a", None).s("a").bytes();
    let b = in_root(STRING, "b", None).s("b").bytes();
    doc.apply_update_from_binary_v1(update(&[(1, 0, vec![a.clone()]), (2, 0, vec![b.clone()])]))
        .unwrap();

    let bridge = Wire::default()
        .b(STRING | HAS_LEFT | HAS_RIGHT)
        .u(1)
        .u(0)
        .u(2)
        .u(0)
        .s("c")
        .bytes();
    let bytes = update(&[(3, 0, vec![bridge.clone()])]);
    assert_eq!(
        doc.apply_update_from_binary_v1(&bytes),
        Err(JwstCodecError::InvalidParent)
    );
    assert_eq!(doc.get_or_create_text("a").unwrap().to_string(), "a");
    assert_eq!(doc.get_or_create_text("b").unwrap().to_string(), "b");

    // ReadDoc rejects the same snapshot instead of linking across lists
    let snapshot = update(&[(1, 0, vec![a]), (2, 0, vec![b]), (3, 0, vec![bridge])]);
    assert_eq!(
        Doc::try_from_binary_v1(&snapshot).err(),
        Some(JwstCodecError::InvalidParent)
    );
    assert!(matches!(
        ReadDoc::from_full_update_v1(snapshot),
        Err(ReadError::InvalidUpdate(JwstCodecError::InvalidParent))
    ));
}

// Like `ReadDoc`, same-client dependencies must precede the item.
#[test]
fn same_client_dependencies_precede_the_item() {
    let first = in_root(STRING, "t", None).s("a").bytes();
    let self_anchored = Wire::default().b(STRING | HAS_RIGHT).u(1).u(1).s("b").bytes();
    let bytes = update(&[(1, 0, vec![first.clone(), self_anchored])]);
    let mut doc = Doc::with_client(9);
    assert_eq!(
        doc.apply_update_from_binary_v1(&bytes),
        Err(JwstCodecError::InvalidParent)
    );
    assert!(matches!(
        ReadDoc::from_full_update_v1(bytes),
        Err(ReadError::InvalidUpdate(JwstCodecError::InvalidParent))
    ));

    // a parent at or after the item is missing, as before
    let own_child = in_item(STRING, Id::new(1, 1), "k").s("b").bytes();
    let bytes = update(&[(1, 0, vec![first.clone(), own_child])]);
    let mut doc = Doc::with_client(9);
    doc.apply_update_from_binary_v1(&bytes).unwrap();
    assert!(doc.store.read().unwrap().get_node(Id::new(1, 1)).unwrap().is_gc());
    let read = ReadDoc::from_full_update_v1(bytes).unwrap();
    assert_eq!(read.text("t").unwrap().to_string(), "a");

    // also when the future struct is a type: the item must not join a map
    // that does not exist yet
    let child = in_item(STRING, Id::new(1, 1), "k").s("b").bytes();
    let map = in_root(TYPE, "m", Some("x")).u(KIND_MAP).bytes();
    let bytes = update(&[(1, 0, vec![child, map])]);
    let doc = Doc::try_from_binary_v1(&bytes).unwrap();
    assert!(doc.store.read().unwrap().get_node(Id::new(1, 0)).unwrap().is_gc());
    let Some(Value::Map(map)) = doc.get_or_create_map("m").unwrap().get("x") else {
        panic!("the map integrates after the dropped child");
    };
    assert!(map.is_empty());
    let read = ReadDoc::from_full_update_v1(bytes).unwrap();
    let map = read.map("m").unwrap().get("x").unwrap().as_map().unwrap();
    assert!(map.is_empty());
}

// Honest overlaps still integrate.
#[test]
fn honest_overlap_still_integrates() {
    let source = Doc::with_client(1);
    let mut text = source.get_or_create_text("t").unwrap();
    text.insert(0, "ab").unwrap();
    let first = source.encode_update_v1().unwrap();
    text.insert(2, "cd").unwrap();
    let mut map = source.get_or_create_map("m").unwrap();
    map.insert("k".into(), "v").unwrap();
    let full = source.encode_update_v1().unwrap();

    let mut target = Doc::with_client(2);
    target.apply_update_from_binary_v1(first).unwrap();
    target.apply_update_from_binary_v1(&full).unwrap();
    target.apply_update_from_binary_v1(&full).unwrap();
    assert_eq!(target.get_or_create_text("t").unwrap().to_string(), "abcd");
    assert_eq!(target.get_or_create_map("m").unwrap().get("k"), Some(Value::from("v")));
    assert_eq!(target.get_state_vector(), source.get_state_vector());
}

/// Runs `f` on a thread whose stack the old recursive delete and GC overflow
/// at the nesting depth used below.
fn on_small_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 10)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

const DEEP: usize = 5_000;

fn deep_arrays(doc: &Doc) -> Array {
    let root = doc.get_or_create_array("root").unwrap();
    let mut current = root.clone();
    for _ in 0..DEEP {
        let child = doc.create_array().unwrap();
        current.push(child.clone()).unwrap();
        current = child;
    }
    current.push(1).unwrap();
    root
}

// Deleting and collecting deeply nested types used to recurse once per
// level.
#[test]
#[cfg_attr(miri, ignore)]
fn deep_nesting_deletes_and_collects_without_recursion() {
    let source = Doc::with_client(1);
    let mut root = deep_arrays(&source);
    let snapshot = source.encode_update_v1().unwrap();

    let mut remote = Doc::with_client(2);
    remote.apply_update_from_binary_v1(&snapshot).unwrap();

    let local = source.clone();
    on_small_stack(move || {
        root.remove(0, 1).unwrap();
        local.gc().unwrap();
        assert!(root.is_empty());
    });

    let deletion = source.encode_update_v1().unwrap();
    on_small_stack(move || {
        remote.apply_update_from_binary_v1(deletion).unwrap();
        remote.gc().unwrap();
        assert!(remote.get_or_create_array("root").unwrap().is_empty());
    });
}

// A format item stored as a map value reads as undefined, as in Yjs,
// whether it names its key or inherits it from its left neighbor.
#[test]
fn format_map_values_read_as_undefined() {
    let explicit = in_root(FORMAT, "m", Some("k")).s("bold").s("true").bytes();
    let value = in_root(ANY, "m", Some("j")).u(1).b(125).u(1).bytes();
    let inherited = Wire::default()
        .b(FORMAT | HAS_LEFT)
        .u(2)
        .u(0)
        .s("italic")
        .s("null")
        .bytes();
    let bytes = update(&[(1, 0, vec![explicit]), (2, 0, vec![value, inherited])]);

    let doc = Doc::try_from_binary_v1(&bytes).unwrap();
    let map = doc.get_or_create_map("m").unwrap();
    assert_eq!(map.get("k"), Some(Value::Any(Any::Undefined)));
    assert_eq!(map.get("j"), Some(Value::Any(Any::Undefined)));
    assert_eq!(map.iter().count(), 2);
    serde_json::to_string(&map).unwrap();

    let read = ReadDoc::from_full_update_v1(bytes).unwrap();
    let map = read.map("m").unwrap();
    assert!(map.get("k").unwrap().as_any().unwrap().is_undefined());
    assert!(map.get("j").unwrap().as_any().unwrap().is_undefined());
    assert!(
        map.values()
            .all(|value| value.as_any().is_some_and(|any| any.is_undefined()))
    );
}

// Yjs spreads any subdocument options it decodes; unexpected shapes must
// fall back to defaults instead of panicking.
#[test]
fn subdocument_options_of_any_shape() {
    let options: [(&str, Vec<u8>, bool); 6] = [
        ("Yjs default", vec![118, 0], true),
        ("gc off", Wire::default().b(118).u(1).s("gc").b(121).bytes(), false),
        ("null", vec![126], true),
        ("integer", vec![125, 0], true),
        ("undefined", vec![127], true),
        (
            "mistyped",
            Wire::default()
                .b(118)
                .u(2)
                .s("gc")
                .b(119)
                .s("no")
                .s("guid")
                .b(125)
                .u(3)
                .bytes(),
            true,
        ),
    ];
    for (name, opts, gc) in options {
        let item = in_root(DOC, "m", Some("d")).s("sub-guid").raw(&opts).bytes();
        let doc = Doc::try_from_binary_v1(update(&[(1, 0, vec![item])])).unwrap();
        let Some(Value::Doc(subdoc)) = doc.get_or_create_map("m").unwrap().get("d") else {
            panic!("{name}: subdocument expected");
        };
        assert_eq!(subdoc.guid(), "sub-guid", "{name}");
        assert_eq!(subdoc.options().gc, gc, "{name}");
    }
}

// A struct count the input cannot hold fails before memory is reserved
// for it, in both decoders.
#[test]
fn declared_counts_beyond_input_fail_early() {
    let bytes = Wire::default().u(1).u(1_999_999).u(1).u(0).bytes();
    assert!(matches!(
        ReadDoc::from_full_update_v1(bytes.clone()),
        Err(ReadError::InvalidUpdate(JwstCodecError::IncompleteDocument(_)))
    ));
    assert!(matches!(
        Update::decode_v1(&bytes),
        Err(JwstCodecError::IncompleteDocument(_))
    ));
}

// A repeated client block replaced the first one's structs (and left
// them orphaned in a ReadDoc); it is rejected instead.
#[test]
fn duplicate_client_blocks_are_rejected() {
    let a = in_root(STRING, "t", None).s("a").bytes();
    let b = Wire::default().b(STRING | HAS_LEFT).u(1).u(0).s("b").bytes();
    let bytes = update(&[(1, 0, vec![a.clone()]), (1, 1, vec![b.clone()])]);

    assert!(Doc::try_from_binary_v1(&bytes).is_err());
    assert!(matches!(
        ReadDoc::from_full_update_v1(bytes),
        Err(ReadError::InvalidUpdate(JwstCodecError::IncompleteDocument(_)))
    ));

    // the same structs in one block are fine
    let bytes = update(&[(1, 0, vec![a, b])]);
    assert_eq!(
        Doc::try_from_binary_v1(&bytes)
            .unwrap()
            .get_or_create_text("t")
            .unwrap()
            .to_string(),
        "ab"
    );
    assert_eq!(
        ReadDoc::from_full_update_v1(bytes)
            .unwrap()
            .text("t")
            .unwrap()
            .to_string(),
        "ab"
    );
}

// The owned update decoder bounds `Any` nesting.
#[test]
fn update_any_nesting_is_bounded() {
    let nested = |depth: usize| {
        let mut bytes = [117u8, 1].repeat(depth);
        bytes.push(126);
        update(&[(1, 0, vec![in_root(ANY, "a", None).u(1).raw(&bytes).bytes()])])
    };
    assert!(Doc::try_from_binary_v1(nested(128)).is_ok());
    assert!(matches!(
        Doc::try_from_binary_v1(nested(129)),
        Err(JwstCodecError::IncompleteDocument(_))
    ));
}
