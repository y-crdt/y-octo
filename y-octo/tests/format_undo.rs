mod support;

use y_octo::{UndoManager, UndoOptions};

#[test]
fn undo_and_redo_leave_preexisting_format_only_gap_alone() {
    use y_octo::{CrdtWriter, Id, RawEncoder};
    let mut e = RawEncoder::default();
    for n in [1, 2, 111, 0] {
        e.write_var_u64(n).unwrap();
    }
    e.write_u8(6).unwrap();
    e.write_var_u64(1).unwrap();
    e.write_var_string("text").unwrap();
    e.write_var_string("bold").unwrap();
    e.write_var_string("true").unwrap();
    e.write_u8(134).unwrap();
    e.write_item_id(&Id::new(111, 0)).unwrap();
    e.write_var_string("bold").unwrap();
    e.write_var_string("null").unwrap();
    e.write_var_u64(0).unwrap();
    let mut doc = support::doc(101, false);
    let mut text = doc.get_or_create_text("text").unwrap();
    doc.apply_update_from_binary_v1(e.into_inner()).unwrap();
    let undo = UndoManager::<()>::new(&doc, [(&text).into()], UndoOptions::default()).unwrap();
    text.insert(0, "a").unwrap();
    undo.undo().unwrap().unwrap();
    assert_eq!(text.to_string(), "");
    assert!(doc.get_delete_sets().get(&111).is_none());
    undo.redo().unwrap().unwrap();
    assert_eq!(text.to_string(), "a");
    assert!(doc.get_delete_sets().get(&111).is_none());
}
