use std::collections::BTreeMap;

use super::*;
use crate::sync::Arc;

fn ds(bytes: &[u8]) -> Vec<(u64, u64, u64)> {
    let mut update = Update::decode_v1(bytes).unwrap();
    let ceiling = StateVector::from([(1, u64::MAX), (2, u64::MAX), (3, u64::MAX), (7, u64::MAX)]);
    let mut out: Vec<_> = update
        .delete_set_iter(ceiling)
        .map(|(client, range)| (client, range.start, range.end - range.start))
        .collect();
    out.sort();
    out
}

#[test]
fn nested_deferred_tx_read_your_writes_and_single_commit() {
    let mut session = DocSession::<Vec<u8>>::new(DocOptions::from_identity(101, "sess".into()), 500);
    let root = session.ensure_root("blocks", YTypeKind::Map).unwrap();

    assert_eq!(session.begin_tx(SessionTxOrigin::Tracked).unwrap(), 1);
    assert!(
        session
            .map_set(&root.clone().into(), "a".into(), SessionValue::Any(1.into()))
            .unwrap()
            .is_none()
    );
    assert_eq!(
        session.get_map_value(&root.clone().into(), "a").unwrap(),
        Some(SessionReadValue::Any(Any::Integer(1)))
    );

    assert_eq!(session.begin_tx(SessionTxOrigin::Untracked).unwrap(), 2);
    assert!(
        session
            .map_set(&root.clone().into(), "b".into(), SessionValue::Any(2.into()))
            .unwrap()
            .is_none()
    );
    assert_eq!(session.commit_tx().unwrap(), None);
    assert_eq!(session.tx_depth(), 1);

    let commit = session.commit_tx().unwrap().expect("outer commit produces event");
    assert_eq!(session.tx_depth(), 0);
    assert!(commit.is_local);
    assert_eq!(commit.origin_kind, SessionOriginKind::LocalTransact);
    assert!(commit.can_undo);
    assert!(!commit.can_redo);
    assert_eq!(commit.changed.len(), 1);
    assert_eq!(commit.changed[0].identity, root);
    assert_eq!(commit.changed[0].keys, vec!["a".to_string(), "b".to_string()]);

    let undone = session.undo().unwrap().expect("undo commit");
    assert_eq!(undone.origin_kind, SessionOriginKind::Undo { stack_id: 0 });
    assert!(undone.origin_kind.is_undo());
    assert!(!undone.can_undo);
    assert!(undone.can_redo);
    assert_eq!(session.get_map_value(&root.clone().into(), "a").unwrap(), None);
    assert_eq!(session.get_map_value(&root.into(), "b").unwrap(), None);
}

#[test]
fn nested_value_and_path_addressing_preserve_unknown_fields() {
    let mut session = DocSession::<Vec<u8>>::new(DocOptions::from_identity(201, "wb".into()), 500);
    let blocks = session.ensure_root("blocks", YTypeKind::Map).unwrap();

    session
        .map_set(
            &blocks.into(),
            "surface-1".into(),
            SessionValue::Map(vec![
                ("sys:flavour".into(), SessionValue::Any("affine:surface".into())),
                (
                    "prop:elements".into(),
                    SessionValue::Map(vec![(
                        "value".into(),
                        SessionValue::Map(vec![(
                            "elem-1".into(),
                            SessionValue::Map(vec![
                                ("type".into(), SessionValue::Any("shape".into())),
                                ("x".into(), SessionValue::Any(10.into())),
                                ("customUnknown".into(), SessionValue::Any("keep-me".into())),
                                (
                                    "text".into(),
                                    SessionValue::Text(vec![TextDeltaOp::Insert {
                                        insert: TextInsert::Text("Hello".into()),
                                        format: None,
                                    }]),
                                ),
                            ]),
                        )]),
                    )]),
                ),
            ]),
        )
        .unwrap();

    let elem_path = TypePath::root("blocks")
        .key("surface-1")
        .key("prop:elements")
        .key("value")
        .key("elem-1");
    let elem_id = session.resolve_path(&elem_path).expect("resolved elem-1");
    let status = session.type_status(&elem_id);
    assert!(status.alive);
    assert_eq!(status.kind, Some(YTypeKind::Map));
    assert_eq!(status.path.as_ref(), Some(&elem_path));

    let commit = session
        .map_set(&elem_path.clone().into(), "x".into(), SessionValue::Any(42.into()))
        .unwrap()
        .unwrap();
    assert_eq!(commit.changed[0].identity, elem_id);
    assert_eq!(commit.changed[0].path.as_ref(), Some(&elem_path));
    assert_eq!(commit.changed[0].keys, vec!["x".to_string()]);

    assert_eq!(
        session.get_map_value(&elem_path.clone().into(), "x").unwrap(),
        Some(SessionReadValue::Any(Any::Integer(42)))
    );
    assert_eq!(
        session
            .get_map_value(&elem_path.clone().into(), "customUnknown")
            .unwrap(),
        Some(SessionReadValue::Any(Any::String("keep-me".into())))
    );

    let text_path = elem_path.key("text");
    assert_eq!(session.read_text_string(&text_path.clone().into()).unwrap(), "Hello");
    session.text_insert(&text_path.clone().into(), 5, " World").unwrap();
    assert_eq!(session.read_text_string(&text_path.into()).unwrap(), "Hello World");
}

#[test]
fn revert_update_v1_restores_and_rejects_invalid_ancestry() {
    let mut s = DocSession::<Vec<u8>>::new(DocOptions::from_identity(10, "rev".into()), 500);
    let text = s.ensure_root("text", YTypeKind::Text).unwrap();
    let meta = s.ensure_root("meta", YTypeKind::Map).unwrap();
    s.text_insert(&text.clone().into(), 0, "hello world").unwrap();
    s.map_set(&meta.clone().into(), "title".into(), SessionValue::Any("v1".into()))
        .unwrap();
    let target_snapshot = s.encode_update_v1().unwrap();

    s.text_remove(&text.clone().into(), 6, 5).unwrap();
    s.text_insert(&text.clone().into(), 6, "rust").unwrap();
    s.map_set(&meta.clone().into(), "title".into(), SessionValue::Any("v2".into()))
        .unwrap();
    s.map_set(&meta.clone().into(), "extra".into(), SessionValue::Any(true.into()))
        .unwrap();
    let current_snapshot = s.encode_update_v1().unwrap();
    assert_eq!(s.read_text_string(&text.clone().into()).unwrap(), "hello rust");

    // Inverted arguments (target > current) must be rejected.
    assert!(matches!(
        revert_update_v1(&target_snapshot, &current_snapshot),
        Err(JwstCodecError::IncompleteDocument(_))
    ));
    // Empty current + non-empty target must be rejected.
    assert!(matches!(
        revert_update_v1(&[0, 0], &target_snapshot),
        Err(JwstCodecError::IncompleteDocument(_))
    ));
    // Snapshot with missing dependency (unresolved pending update) must be
    // rejected.
    let mut s_dep = DocSession::<Vec<u8>>::new(DocOptions::from_identity(11, "dep".into()), 0);
    let dt = s_dep.ensure_root("t", YTypeKind::Text).unwrap();
    s_dep.text_insert(&dt.clone().into(), 0, "ab").unwrap();
    let sv1 = s_dep.encode_state_vector_v1().unwrap();
    s_dep.text_insert(&dt.into(), 2, "cd").unwrap();
    let partial_delta = s_dep.encode_diff_v1(&sv1).unwrap();
    assert!(matches!(
        revert_update_v1(&partial_delta, &[0, 0]),
        Err(JwstCodecError::IncompleteDocument(_))
    ));

    // Valid revert works cleanly.
    let revert_delta = revert_update_v1(&current_snapshot, &target_snapshot).unwrap();
    s.apply_update_v1(&revert_delta).unwrap();
    assert_eq!(s.read_text_string(&text.into()).unwrap(), "hello world");
    assert_eq!(
        s.get_map_value(&meta.clone().into(), "title").unwrap(),
        Some(SessionReadValue::Any(Any::String("v1".into())))
    );
    assert_eq!(s.get_map_value(&meta.into(), "extra").unwrap(), None);
}

#[test]
fn disabled_undo_installs_zero_history_hook() {
    let mut session = DocSession::<Vec<u8>>::with_config(
        DocOptions::from_identity(11, "no-undo".into()),
        SessionConfig {
            undo: SessionUndoConfig::Disabled,
        },
    );
    {
        let store = read_store(&session.doc_ref().store).unwrap();
        assert!(store.history_hook.is_none());
    }
    let text = session.ensure_root("t", YTypeKind::Text).unwrap();
    let c = session.text_insert(&text.into(), 0, "abc").unwrap().unwrap();
    assert!(!c.can_undo);
    assert!(!c.can_redo);
    assert!(!session.can_undo());
    assert!(!session.can_redo());
    assert_eq!(session.undo().unwrap(), None);
    assert_eq!(session.redo().unwrap(), None);
    {
        let store = read_store(&session.doc_ref().store).unwrap();
        assert!(store.history_hook.is_none());
    }
}

#[test]
fn dual_subtree_undo_stacks_and_destroy_preserve_retained_items_across_gc() {
    let mut session = DocSession::<Vec<u8>>::with_config(
        DocOptions::from_identity(12, "dual-gc".into()).auto_gc(true),
        SessionConfig {
            undo: SessionUndoConfig::Custom,
        },
    );
    let text_a = session.ensure_root("a", YTypeKind::Text).unwrap();
    let text_b = session.ensure_root("b", YTypeKind::Text).unwrap();

    let stack_a = session
        .create_undo_stack(&[text_a.clone().into()], 0, &[SessionTxOrigin::Tracked])
        .unwrap();
    let stack_b = session
        .create_undo_stack(&[text_b.clone().into()], 0, &[SessionTxOrigin::Tracked])
        .unwrap();

    session.text_insert(&text_a.clone().into(), 0, "alpha-content").unwrap();
    session.text_insert(&text_b.clone().into(), 0, "beta-content").unwrap();

    session.text_remove(&text_a.clone().into(), 0, 13).unwrap();
    session.text_remove(&text_b.clone().into(), 0, 12).unwrap();

    // Destroy stack B via maintenance tx (and trigger GC). Stack A's retained
    // deletion must survive!
    assert!(session.destroy_undo_stack(stack_b).unwrap());
    assert!(!session.destroy_undo_stack(stack_b).unwrap());
    assert!(!session.can_undo_stack(stack_b));

    // Subsequent edit works cleanly without leftover collector.merges.
    session.text_insert(&text_b.clone().into(), 0, "fresh").unwrap();

    // Creating a new stack gets a monotonically increasing ID (never reuses
    // destroyed stack_b's ID), and stale stack_b calls cannot affect stack_c.
    let stack_c = session
        .create_undo_stack(&[text_b.clone().into()], 0, &[SessionTxOrigin::Tracked])
        .unwrap();
    assert_ne!(stack_c, stack_b);
    assert_eq!(session.undo_stack(stack_b).unwrap(), None);
    assert_eq!(
        session.clear_stack_history(stack_b, true, true).unwrap_err(),
        JwstCodecError::InvalidParent
    );
    session.text_insert(&text_b.clone().into(), 5, "!").unwrap();
    assert!(session.can_undo_stack(stack_c));
    assert_eq!(session.undo_stack(stack_b).unwrap(), None);
    assert!(session.can_undo_stack(stack_c));

    // Stack A still restores its deleted content!
    assert!(session.can_undo_stack(stack_a));
    let undo_a = session.undo_stack(stack_a).unwrap().expect("undo A survives GC");
    assert_eq!(undo_a.origin_kind, SessionOriginKind::Undo { stack_id: stack_a.0 });
    assert_eq!(session.read_text_string(&text_a.into()).unwrap(), "alpha-content");
}

#[test]
fn named_origin_routes_to_specific_undo_stack() {
    let mut session = DocSession::<Vec<u8>>::with_config(
        DocOptions::from_identity(13, "named".into()),
        SessionConfig {
            undo: SessionUndoConfig::Custom,
        },
    );
    let m = session.ensure_root("m", YTypeKind::Map).unwrap();
    let origin_ai = SessionTxOrigin::Named(SmolStr::new("ai-agent"));
    let origin_user = SessionTxOrigin::Named(SmolStr::new("user"));

    let ai_stack = session
        .create_undo_stack(&[], 0, std::slice::from_ref(&origin_ai))
        .unwrap();
    let user_stack = session
        .create_undo_stack(&[], 0, std::slice::from_ref(&origin_user))
        .unwrap();

    session.begin_tx(origin_user.clone()).unwrap();
    session
        .map_set(&m.clone().into(), "k_user".into(), SessionValue::Any(1.into()))
        .unwrap();
    let c_user = session.commit_tx().unwrap().unwrap();
    assert_eq!(c_user.origin_kind, SessionOriginKind::LocalNamed("user".into()));

    session.begin_tx(origin_ai.clone()).unwrap();
    session
        .map_set(&m.clone().into(), "k_ai".into(), SessionValue::Any(2.into()))
        .unwrap();
    let c_ai = session.commit_tx().unwrap().unwrap();
    assert_eq!(c_ai.origin_kind, SessionOriginKind::LocalNamed("ai-agent".into()));

    assert!(session.can_undo_stack(ai_stack));
    assert!(session.can_undo_stack(user_stack));

    let u_ai = session.undo_stack(ai_stack).unwrap().unwrap();
    assert_eq!(u_ai.origin_kind, SessionOriginKind::Undo { stack_id: ai_stack.0 });
    assert_eq!(session.get_map_value(&m.clone().into(), "k_ai").unwrap(), None);
    assert_eq!(
        session.get_map_value(&m.clone().into(), "k_user").unwrap(),
        Some(SessionReadValue::Any(Any::Integer(1)))
    );

    let r_ai = session.redo_stack(ai_stack).unwrap().unwrap();
    assert_eq!(r_ai.origin_kind, SessionOriginKind::Redo { stack_id: ai_stack.0 });
    assert!(r_ai.origin_kind.is_redo());
    assert_eq!(
        session.get_map_value(&m.into(), "k_ai").unwrap(),
        Some(SessionReadValue::Any(Any::Integer(2)))
    );
}

#[test]
fn from_update_v1_into_doc_and_open_tx_guards() {
    let doc = DocOptions::from_identity(14, "src".into()).build();
    doc.get_or_create_text("t").unwrap().insert(0, "ok").unwrap();
    let snap = doc.encode_update_v1().unwrap();

    let mut session = DocSession::<Vec<u8>>::from_update_v1(
        &snap,
        DocOptions::from_identity(15, "dst".into()),
        SessionConfig::default(),
    )
    .unwrap();
    let root = session.ensure_root("t", YTypeKind::Text).unwrap();
    assert_eq!(session.read_text_string(&root.clone().into()).unwrap(), "ok");

    session.begin_tx(SessionTxOrigin::Tracked).unwrap();
    assert_eq!(
        session.apply_update_v1(&[]).unwrap_err(),
        JwstCodecError::OpenTransactionFrame
    );
    assert_eq!(session.undo().unwrap_err(), JwstCodecError::OpenTransactionFrame);
    assert_eq!(session.redo().unwrap_err(), JwstCodecError::OpenTransactionFrame);
    assert_eq!(
        session.destroy_undo_stack(UndoStackId(0)).unwrap_err(),
        JwstCodecError::OpenTransactionFrame
    );
    assert_eq!(
        session.clear_history(true, true).unwrap_err(),
        JwstCodecError::OpenTransactionFrame
    );

    session.commit_tx().unwrap();
    let doc_back = session.into_doc().unwrap();
    assert_eq!(doc_back.get_or_create_text("t").unwrap().to_string(), "ok");
}

#[test]
fn into_doc_rejects_open_tx_and_drop_does_not_silently_commit() {
    let mut s1 = DocSession::<Vec<u8>>::new(DocOptions::from_identity(15, "open".into()), 500);
    s1.begin_tx(SessionTxOrigin::Tracked).unwrap();
    assert!(matches!(s1.into_doc(), Err(JwstCodecError::OpenTransactionFrame)));

    let mut s2 = DocSession::<Vec<u8>>::new(DocOptions::from_identity(16, "drop-no-commit".into()), 500);
    let store_weak = Arc::downgrade(&s2.doc_ref().store);
    let m = s2.ensure_root("m", YTypeKind::Map).unwrap();
    s2.begin_tx(SessionTxOrigin::Tracked).unwrap();
    s2.map_set(&m.into(), "k".into(), SessionValue::Any(1.into())).unwrap();
    {
        let store = read_store(&s2.doc_ref().store).unwrap();
        assert_eq!(store.commit_seq, 0);
    }
    assert!(!s2.can_undo());
    drop(s2);
    assert!(store_weak.upgrade().is_none());
}

#[test]
fn container_kind_mismatch_and_unknown_solidification() {
    let mut s = DocSession::<Vec<u8>>::new(DocOptions::from_identity(17, "kinds".into()), 500);
    let map = s.ensure_root("m", YTypeKind::Map).unwrap();
    let arr = s.ensure_root("a", YTypeKind::Array).unwrap();
    let txt = s.ensure_root("t", YTypeKind::Text).unwrap();
    let elem = s.ensure_root("el", YTypeKind::XMLElement).unwrap();

    assert!(matches!(
        s.get_map_value(&arr.clone().into(), "k"),
        Err(JwstCodecError::UnexpectedType(_))
    ));
    assert!(matches!(
        s.read_map(&txt.clone().into()),
        Err(JwstCodecError::UnexpectedType(_))
    ));
    assert!(matches!(
        s.map_set(&elem.clone().into(), "k".into(), SessionValue::Any(1.into())),
        Err(JwstCodecError::UnexpectedType(_))
    ));

    assert!(matches!(
        s.read_array(&map.clone().into()),
        Err(JwstCodecError::UnexpectedType(_))
    ));
    assert!(matches!(
        s.array_push(&txt.clone().into(), vec![SessionValue::Any(1.into())]),
        Err(JwstCodecError::UnexpectedType(_))
    ));

    assert!(matches!(
        s.read_text_string(&map.into()),
        Err(JwstCodecError::UnexpectedType(_))
    ));
    assert!(matches!(
        s.text_insert(&arr.into(), 0, "hi"),
        Err(JwstCodecError::UnexpectedType(_))
    ));
    assert!(matches!(
        s.xml_set_attr(&txt.into(), "id".into(), "x".into()),
        Err(JwstCodecError::UnexpectedType(_))
    ));

    // Unknown root solidifies on first write and rejects conflicting ops after.
    let unk = s.ensure_root("u", YTypeKind::Unknown).unwrap();
    s.map_set(&unk.clone().into(), "k".into(), SessionValue::Any(1.into()))
        .unwrap();
    assert!(matches!(
        s.array_push(&unk.into(), vec![SessionValue::Any(2.into())]),
        Err(JwstCodecError::UnexpectedType(_))
    ));
}

#[test]
fn xml_nested_tree_attrs_to_string_and_undo_redo() {
    let mut s = DocSession::<Vec<u8>>::new(DocOptions::from_identity(18, "xml".into()), 0);
    let frag = s.ensure_root("prosemirror", YTypeKind::XMLFragment).unwrap();

    let mut bold = BTreeMap::new();
    bold.insert("b".to_string(), Any::True);

    s.array_push(
        &frag.clone().into(),
        vec![SessionValue::XmlElement {
            tag: "p".into(),
            attrs: vec![("class".into(), "lead".into())],
            children: vec![
                SessionValue::XmlText(vec![TextDeltaOp::Insert {
                    insert: TextInsert::Text("Hello ".into()),
                    format: None,
                }]),
                SessionValue::XmlElement {
                    tag: "span".into(),
                    attrs: vec![],
                    children: vec![SessionValue::XmlText(vec![TextDeltaOp::Insert {
                        insert: TextInsert::Text("world".into()),
                        format: Some(bold),
                    }])],
                },
            ],
        }],
    )
    .unwrap();

    assert_eq!(
        s.xml_to_string(&frag.clone().into()).unwrap(),
        "<p class=\"lead\">Hello <span><b>world</b></span></p>"
    );

    let p_path = TypePath::root("prosemirror").index(0);
    assert_eq!(s.xml_name(&p_path.clone().into()).unwrap(), "p");
    assert_eq!(
        s.xml_get_attr(&p_path.clone().into(), "class").unwrap(),
        Some(Any::String("lead".into()))
    );

    s.xml_set_attr(&p_path.clone().into(), "id".into(), "p1".into())
        .unwrap();
    assert_eq!(
        s.xml_attrs(&p_path.clone().into()).unwrap(),
        vec![
            ("class".into(), Any::String("lead".into())),
            ("id".into(), Any::String("p1".into())),
        ]
    );
    assert_eq!(
        s.xml_to_string(&p_path.clone().into()).unwrap(),
        "<p class=\"lead\" id=\"p1\">Hello <span><b>world</b></span></p>"
    );

    let txt_path = p_path.clone().index(0);
    let mut italic = BTreeMap::new();
    italic.insert("i".to_string(), Any::True);
    s.text_format(&txt_path.into(), 0, 5, italic).unwrap();
    assert_eq!(
        s.xml_to_string(&p_path.clone().into()).unwrap(),
        "<p class=\"lead\" id=\"p1\"><i>Hello</i> <span><b>world</b></span></p>"
    );

    s.undo().unwrap().expect("undo format");
    assert_eq!(
        s.xml_to_string(&p_path.clone().into()).unwrap(),
        "<p class=\"lead\" id=\"p1\">Hello <span><b>world</b></span></p>"
    );
    s.undo().unwrap().expect("undo id attr");
    assert_eq!(s.xml_get_attr(&p_path.clone().into(), "id").unwrap(), None);

    s.redo().unwrap().expect("redo id attr");
    assert_eq!(
        s.xml_get_attr(&p_path.into(), "id").unwrap(),
        Some(Any::String("p1".into()))
    );

    // Verify XMLHook root & map ops
    let hook = s.ensure_root("h", YTypeKind::XMLHook).unwrap();
    s.map_set(&hook.clone().into(), "k".into(), SessionValue::Any(99.into()))
        .unwrap();
    assert_eq!(
        s.get_map_value(&hook.into(), "k").unwrap(),
        Some(SessionReadValue::Any(Any::Integer(99)))
    );
}

// ---------------------------------------------------------------------------
// Fable review regression probes (p2, p2b, p3, p3b, p4)

#[test]
fn p2_standalone_text_delta_failure_leaves_zero_mutation() {
    let mut s = DocSession::<Vec<u8>>::new(DocOptions::from_identity(7, "probe".into()), 0);
    let target: TypeTarget = s.ensure_root("t", YTypeKind::Text).unwrap().into();
    let sv_before = s.encode_state_vector_v1().unwrap();
    let res = s.text_apply_delta(
        &target,
        &[
            TextDeltaOp::Insert {
                insert: TextInsert::Text("abc".into()),
                format: None,
            },
            TextDeltaOp::Retain {
                retain: 100,
                format: None,
            },
        ],
    );
    assert!(matches!(res, Err(JwstCodecError::IndexOutOfBound(100))));
    assert_eq!(s.read_text_string(&target).unwrap(), "");
    assert_eq!(s.encode_state_vector_v1().unwrap(), sv_before);
    assert!(!s.can_undo());
}

#[test]
fn p2b_nested_value_failure_leaves_zero_mutation() {
    let mut s = DocSession::<Vec<u8>>::new(DocOptions::from_identity(7, "probe".into()), 0);
    let root: TypeTarget = s.ensure_root("m", YTypeKind::Map).unwrap().into();
    let res = s.map_set(
        &root,
        "k".into(),
        SessionValue::Map(vec![
            ("a".into(), SessionValue::Any(Any::Integer(1))),
            (
                "t".into(),
                SessionValue::Text(vec![TextDeltaOp::Retain {
                    retain: 5,
                    format: None,
                }]),
            ),
        ]),
    );
    assert!(matches!(res, Err(JwstCodecError::IndexOutOfBound(5))));
    assert_eq!(s.get_map_value(&root, "k").unwrap(), None);
    assert!(!s.can_undo());
}

#[test]
fn p3_clear_history_then_edit_drains_collector_merges() {
    let mut s = DocSession::<Vec<u8>>::new(DocOptions::from_identity(7, "probe".into()), 0);
    let root: TypeTarget = s.ensure_root("m", YTypeKind::Map).unwrap().into();
    s.map_set(
        &root,
        "k".into(),
        SessionValue::Map(vec![
            ("a".into(), SessionValue::Any(Any::Integer(1))),
            ("b".into(), SessionValue::Any(Any::Integer(2))),
        ]),
    )
    .unwrap();
    s.map_remove(&root, "k").unwrap();
    s.clear_history(true, true).unwrap();
    s.map_set(&root, "x".into(), SessionValue::Any(Any::Integer(3)))
        .unwrap();
    assert_eq!(
        s.get_map_value(&root, "x").unwrap(),
        Some(SessionReadValue::Any(Any::Integer(3)))
    );
}

#[test]
fn p3b_into_doc_then_edit_drains_collector_merges() {
    let mut s = DocSession::<Vec<u8>>::new(DocOptions::from_identity(7, "probe".into()), 0);
    let root: TypeTarget = s.ensure_root("m", YTypeKind::Map).unwrap().into();
    s.map_set(
        &root,
        "k".into(),
        SessionValue::Map(vec![
            ("a".into(), SessionValue::Any(Any::Integer(1))),
            ("b".into(), SessionValue::Any(Any::Integer(2))),
        ]),
    )
    .unwrap();
    s.map_remove(&root, "k").unwrap();
    let doc = s.into_doc().unwrap();
    let mut m = doc.get_or_create_map("m").unwrap();
    m.insert("x".to_string(), 3).unwrap();
    assert_eq!(m.get("x"), Some(Value::Any(Any::Integer(3))));
}

#[test]
fn p4_remote_apply_emits_separate_local_formatting_cleanup_commit() {
    let mut s = DocSession::<Vec<u8>>::new(DocOptions::from_identity(1, "probe".into()), 0);
    let t: TypeTarget = s.ensure_root("t", YTypeKind::Text).unwrap().into();
    let c1 = s.text_insert(&t, 0, "hello").unwrap().unwrap();

    let bold = TextAttributes::from([("bold".to_string(), Any::True)]);
    let mut peer = DocOptions::from_identity(2, "probe".into()).build();
    peer.apply_update_from_binary_v1(&c1.update).unwrap();
    let mut peer_text = peer.get_or_create_text("t").unwrap();
    let peer_before = peer.get_state_vector();
    peer_text
        .apply_delta(&[TextDeltaOp::Retain {
            retain: 5,
            format: Some(bold.clone()),
        }])
        .unwrap();
    let from_peer = peer.encode_state_as_update_v1(&peer_before).unwrap();

    let c2 = s.text_format(&t, 0, 5, bold).unwrap().unwrap();
    let commits = s.apply_update_v1(&from_peer).unwrap();
    assert_eq!(commits.len(), 2, "remote update + local FormattingCleanup commit");
    assert!(!commits[0].is_local);
    assert_eq!(commits[0].origin_kind, SessionOriginKind::RemoteSync);
    assert!(commits[1].is_local);
    assert_eq!(commits[1].origin_kind, SessionOriginKind::FormattingCleanup);
    assert_eq!(commits[1].revision, commits[0].revision + 1);
    let c3 = s.text_insert(&t, 0, "x").unwrap().unwrap();

    let log = merge_updates_v1([
        c1.update.as_slice(),
        c2.update.as_slice(),
        from_peer.as_slice(),
        commits[0].update.as_slice(),
        commits[1].update.as_slice(),
        c3.update.as_slice(),
    ])
    .unwrap()
    .encode_v1()
    .unwrap();
    let full = s.encode_update_v1().unwrap();
    assert_eq!(c3.revision, commits[1].revision + 1);
    assert_eq!(ds(&log), ds(&full));

    // Broadcasting local commits (c2, commits[1] cleanup, c3) to peer converges
    // delete sets.
    peer.apply_update_from_binary_v1(&c2.update).unwrap();
    peer.apply_update_from_binary_v1(&commits[1].update).unwrap();
    peer.apply_update_from_binary_v1(&c3.update).unwrap();
    assert_eq!(ds(&peer.encode_update_v1().unwrap()), ds(&full));
}

fn seeded_update_for_undeclared_root_reads() -> Vec<u8> {
    let doc = DocOptions::from_identity(9, "seed".into()).build();
    let mut meta = doc.get_or_create_map("meta").unwrap();
    meta.insert("name".to_string(), "workspace").unwrap();
    let mut pages = doc.get_or_create_array("pages").unwrap();
    pages.push("p1").unwrap();
    let mut title = doc.get_or_create_text("title").unwrap();
    title.insert(0, "hello").unwrap();
    let mut xml = doc.get_or_create_xml_fragment("xml").unwrap();
    let p = doc.create_xml_element("p").unwrap();
    xml.push(p).unwrap();
    doc.encode_update_v1().unwrap()
}

#[test]
fn q1_reads_of_undeclared_roots_do_not_silently_return_empty() {
    let s = DocSession::<Vec<u8>>::from_update_v1(
        &seeded_update_for_undeclared_root_reads(),
        DocOptions::from_identity(1, "probe".into()),
        SessionConfig::default(),
    )
    .unwrap();
    let meta: TypeTarget = TypeIdentity::Root("meta".into()).into();
    let pages: TypeTarget = TypePath::root("pages").into();
    let title: TypeTarget = TypeIdentity::Root("title".into()).into();
    let xml_id = TypeIdentity::Root("xml".into());
    let xml: TypeTarget = xml_id.clone().into();

    assert_eq!(
        s.read_map(&meta).unwrap(),
        vec![(
            "name".to_string(),
            SessionReadValue::Any(Any::String("workspace".into()))
        )]
    );
    assert_eq!(
        s.get_map_value(&meta, "name").unwrap(),
        Some(SessionReadValue::Any(Any::String("workspace".into())))
    );
    assert_eq!(
        s.read_array(&pages).unwrap(),
        vec![SessionReadValue::Any(Any::String("p1".into()))]
    );
    assert_eq!(
        s.read_array_at(&pages, 0).unwrap(),
        Some(SessionReadValue::Any(Any::String("p1".into())))
    );
    assert_eq!(s.read_text_string(&title).unwrap(), "hello");
    assert_eq!(s.read_text_len(&title).unwrap(), 5);
    assert_eq!(s.xml_to_string(&xml).unwrap(), "<p></p>");
    assert_eq!(s.type_status(&xml_id).kind, Some(YTypeKind::Unknown));
}

#[test]
fn q2_path_through_undeclared_root() {
    let doc = DocOptions::from_identity(9, "seed".into()).build();
    let mut blocks = doc.get_or_create_map("blocks").unwrap();
    let mut b1 = doc.create_map().unwrap();
    blocks.insert("b1".to_string(), b1.clone()).unwrap();
    b1.insert("flavour".to_string(), "affine:page").unwrap();
    let update = doc.encode_update_v1().unwrap();

    let mut s = DocSession::<Vec<u8>>::from_update_v1(
        &update,
        DocOptions::from_identity(1, "probe".into()),
        SessionConfig::default(),
    )
    .unwrap();
    let nested: TypeTarget = TypePath {
        root: "blocks".into(),
        segments: vec![PathSegment::Key("b1".into())],
    }
    .into();
    assert_eq!(
        s.get_map_value(&nested, "flavour").unwrap(),
        Some(SessionReadValue::Any(Any::String("affine:page".into())))
    );
    assert!(
        s.map_set(&nested, "x".into(), SessionValue::Any(Any::Integer(1)))
            .unwrap()
            .is_some()
    );
    let root: TypeTarget = TypeIdentity::Root("blocks".into()).into();
    let entries = s.read_map(&root).unwrap();
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].0, "b1");
}

#[test]
fn failed_write_does_not_solidify_unknown_root_or_leak_types() {
    let doc = DocOptions::from_identity(9, "seed".into()).build();
    let mut arr = doc.get_or_create_array("items").unwrap();
    arr.push(10).unwrap();
    arr.push(20).unwrap();
    let update = doc.encode_update_v1().unwrap();

    let mut s = DocSession::<Vec<u8>>::from_update_v1(
        &update,
        DocOptions::from_identity(1, "probe".into()),
        SessionConfig::default(),
    )
    .unwrap();
    let root_id = TypeIdentity::Root("items".into());
    let root: TypeTarget = root_id.clone().into();
    assert_eq!(s.type_status(&root_id).kind, Some(YTypeKind::Unknown));

    // Out-of-bounds text delta on Unknown root must fail without solidifying it
    // to Text.
    let err = s
        .text_apply_delta(
            &root,
            &[TextDeltaOp::Retain {
                retain: 4,
                format: None,
            }],
        )
        .unwrap_err();
    assert!(matches!(err, JwstCodecError::IndexOutOfBound(_)));
    assert_eq!(s.type_status(&root_id).kind, Some(YTypeKind::Unknown));

    // Subsequent ensure_root as Array succeeds and reads real data.
    s.ensure_root("items", YTypeKind::Array).unwrap();
    assert_eq!(
        s.read_array(&root).unwrap(),
        vec![
            SessionReadValue::Any(Any::Integer(10)),
            SessionReadValue::Any(Any::Integer(20)),
        ]
    );

    // Mismatched map_set on Text root must not leave a child in the store's
    // type arena.
    let text_root: TypeTarget = s.ensure_root("t", YTypeKind::Text).unwrap().into();
    let types_before = {
        let store = read_store(&s.doc_ref().store).unwrap();
        store.type_arena.len()
    };
    let err = s
        .map_set(
            &text_root,
            "k".into(),
            SessionValue::Map(vec![("a".into(), SessionValue::Any(Any::Integer(1)))]),
        )
        .unwrap_err();
    assert!(matches!(err, JwstCodecError::UnexpectedType(_)));
    let types_after = {
        let store = read_store(&s.doc_ref().store).unwrap();
        store.type_arena.len()
    };
    assert_eq!(types_before, types_after);
}

#[test]
fn a_write_that_does_not_fit_the_type_arena_changes_nothing() {
    let mut s = DocSession::<Vec<u8>>::new(DocOptions::from_identity(1, "full".into()), 500);
    let map: TypeTarget = s.ensure_root("map", YTypeKind::Map).unwrap().into();
    let list: TypeTarget = s.ensure_root("list", YTypeKind::Array).unwrap().into();
    let text = || SessionValue::Text(Vec::new());
    // room for two more types
    let types = {
        let mut store = write_store(&s.doc_ref().store).unwrap();
        let types = store.type_arena.len();
        store.type_arena.set_limit(Some(types + 2));
        types
    };
    let before = s.encode_update_v1().unwrap();
    let unchanged = |s: &DocSession<Vec<u8>>| {
        let store = read_store(&s.doc_ref().store).unwrap();
        assert_eq!(store.type_arena.len(), types);
        assert!(store.collector.is_empty());
        drop(store);
        assert_eq!(s.encode_update_v1().unwrap(), before);
    };

    // three nested types: the outer two would fit
    let nested = SessionValue::Map(vec![(
        "inner".into(),
        SessionValue::Array(vec![SessionValue::Any(Any::Integer(1)), text()]),
    )]);
    assert!(matches!(
        s.map_set(&map, "k".into(), nested.clone()),
        Err(JwstCodecError::IncompleteDocument(_))
    ));
    unchanged(&s);

    // a batch of three: the first two would fit
    for push in [true, false] {
        let batch = vec![text(), text(), text()];
        let result = if push {
            s.array_push(&list, batch)
        } else {
            s.array_insert(&list, 0, batch)
        };
        assert!(matches!(result, Err(JwstCodecError::IncompleteDocument(_))));
        unchanged(&s);
    }
    assert_eq!(s.read_array(&list).unwrap(), vec![]);

    // what fits is written, and the kind check still comes first
    assert!(matches!(
        s.map_set(&list, "k".into(), nested.clone()),
        Err(JwstCodecError::UnexpectedType(_))
    ));
    assert!(s.array_push(&list, vec![text(), text()]).unwrap().is_some());
    assert_eq!(s.read_array(&list).unwrap().len(), 2);
    write_store(&s.doc_ref().store).unwrap().type_arena.set_limit(None);
    assert!(s.map_set(&map, "k".into(), nested).unwrap().is_some());
    assert_eq!(read_store(&s.doc_ref().store).unwrap().type_arena.len(), types + 5);
}

#[test]
fn legacy_content_json_reads_elements_for_array_and_map() {
    use crate::doc::codec::RawEncoder;

    // Hand-craft a minimal V1 update with Content::Json (tag 2) items:
    // - root array "arr": [Some("1"), Some("\"tail\""), None] (len 3)
    // - root map "mp" key "k": [Some("1"), Some("\"last\"")] (len 2)
    let mut enc = RawEncoder::default();
    // 1 client
    enc.write_var_u64(1).unwrap();
    // 2 structs for client 7, starting at clock 0
    enc.write_var_u64(2).unwrap();
    enc.write_var_u64(7).unwrap();
    enc.write_var_u64(0).unwrap();

    // Struct 0: info = has_parent_name (0x20) | Content::Json (2) = 0x22
    // Wait: V1 info bits: 0..5 = content tag (2), bit 5 (0x20) = parent_sub,
    // bit 6 (0x40) = right_origin, bit 7 (0x80) = left_origin.
    // Neither left nor right origin => parent follows: 1 = named root ("arr").
    enc.write_u8(2).unwrap();
    enc.write_u8(1).unwrap();
    enc.write_var_string("arr").unwrap();
    // Content::Json: len = 4, elements: "1", "\"tail\"", "undefined",
    // "0.36442474781641604"
    enc.write_var_u64(4).unwrap();
    enc.write_var_string("1").unwrap();
    enc.write_var_string("\"tail\"").unwrap();
    enc.write_var_string("undefined").unwrap();
    enc.write_var_string("0.36442474781641604").unwrap();

    // Struct 1: info = ITEM_HAS_PARENT_SUB (0x20) | Content::Json (2)
    enc.write_u8(0x20 | 2).unwrap();
    enc.write_u8(1).unwrap();
    enc.write_var_string("mp").unwrap();
    enc.write_var_string("k").unwrap();
    enc.write_var_u64(2).unwrap();
    enc.write_var_string("1").unwrap();
    enc.write_var_string("\"last\"").unwrap();

    // Empty delete set
    enc.write_var_u64(0).unwrap();

    let bytes = enc.into_inner();
    let s = DocSession::<Vec<u8>>::from_update_v1(
        &bytes,
        DocOptions::from_identity(1, "json-legacy".into()),
        SessionConfig::default(),
    )
    .unwrap();

    let arr: TypeTarget = TypeIdentity::Root("arr".into()).into();
    let expected_f64 = 0.36442474781641604_f64;
    let elems = s.read_array(&arr).unwrap();
    assert_eq!(
        elems,
        vec![
            SessionReadValue::Any(Any::Integer(1)),
            SessionReadValue::Any(Any::String("tail".into())),
            SessionReadValue::Any(Any::Undefined),
            SessionReadValue::Any(Any::Float64(expected_f64.into())),
        ]
    );
    match &elems[3] {
        SessionReadValue::Any(Any::Float64(v)) => assert_eq!(v.0.to_bits(), expected_f64.to_bits()),
        other => panic!("expected Float64, got {other:?}"),
    }
    assert_eq!(
        s.read_array_at(&arr, 0).unwrap(),
        Some(SessionReadValue::Any(Any::Integer(1)))
    );
    assert_eq!(
        s.read_array_at(&arr, 1).unwrap(),
        Some(SessionReadValue::Any(Any::String("tail".into())))
    );
    assert_eq!(
        s.read_array_at(&arr, 2).unwrap(),
        Some(SessionReadValue::Any(Any::Undefined))
    );
    match s.read_array_at(&arr, 3).unwrap() {
        Some(SessionReadValue::Any(Any::Float64(v))) => assert_eq!(v.0.to_bits(), expected_f64.to_bits()),
        other => panic!("expected Some(Float64), got {other:?}"),
    }

    let mp: TypeTarget = TypeIdentity::Root("mp".into()).into();
    assert_eq!(
        s.get_map_value(&mp, "k").unwrap(),
        Some(SessionReadValue::Any(Any::String("last".into())))
    );
}
