mod support;
use serde_json::json;
use y_octo::{StateVector, TextDeltaOp};
#[test]
fn format_tail_matches_yjs_at_the_end_of_the_range() {
    let mut doc = support::doc(303, false);
    let mut text = doc.get_or_create_text("text").unwrap();
    let wire = support::bytes(&json!("0205ca010046650004626f6c640566616c7365c6ca01006500046c696e6b0f7b2268726566223a2272656631227dc66500650104626f6c64046e756c6cc6ca01026501046c696e6b046e756c6c44ca010001780c650004010474657874016184650001628465010663646566676846650004626f6c640474727565c665086500046c696e6b0f7b2268726566223a2272656630227dc66500650104626f6c64046e756c6cc6650a6501046c696e6b046e756c6c46650804626f6c640566616c7365c6650c6508046c696e6b0f7b2268726566223a2272656632227dc66500650a04626f6c640474727565c6650e650a046c696e6b0f7b2268726566223a2272656630227d44650c017801650201010802"));
    doc.apply_update_from_binary_v1(wire).unwrap();
    doc.set_client(101);
    let op: TextDeltaOp =
        serde_json::from_value(json!({"retain":1,"format":{"bold":false,"link":{"href":"ref0"}}})).unwrap();
    text.apply_delta(&[op]).unwrap();
    assert_eq!(doc.get_state_vector(), StateVector::from([(101, 20), (202, 5)]));
    assert_eq!(
        support::snapshot(&doc)["delete_set"],
        json!([[101, [[1, 1], [8, 2], [12, 1]]]])
    );
}
