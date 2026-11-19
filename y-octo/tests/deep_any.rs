//! Public-API checks of nested `Any` limits and of moving values out of `Any`.
use y_octo::{
    AHashMap, Any, CrdtWrite, Doc, DocOptions, JwstCodecError, RawDecoder, RawEncoder, ReadDoc, ReadError, ReadLimits,
    Update,
};

/// `depth` arrays nested around `{ leaf: 42 }`, like Yjs `[[{ leaf: 42 }]]`.
fn nested(depth: usize) -> Any {
    let mut value = Any::Object(Box::new(AHashMap::from_iter([("leaf".to_string(), Any::Integer(42))])));
    for _ in 0..depth {
        value = Any::Array(vec![value]);
    }
    value
}

/// Arrays around the leaf object, or `None` when the shape differs.
fn depth_of(mut value: &Any) -> Option<usize> {
    let mut depth = 0;
    while let Any::Array(values) = value {
        let [inner] = values.as_slice() else { return None };
        value = inner;
        depth += 1;
    }
    let Any::Object(map) = value else { return None };
    (map.len() == 1 && map.get("leaf") == Some(&Any::Integer(42))).then_some(depth)
}

fn doc(client: u64) -> Doc {
    DocOptions::from_identity(client, "deep-any".into()).build()
}

/// An update setting `root.deep` to `value`.
fn update_with(value: Any) -> Vec<u8> {
    let doc = doc(7);
    let mut map = doc.get_or_create_map("root").unwrap();
    // `Map::insert` stores the elements of an array as the entry's
    // `ContentAny`; wrap the value so the entry holds exactly `value`, as
    // Yjs `map.set` does.
    map.insert("deep".into(), Any::Array(vec![value])).unwrap();
    doc.encode_update_v1().unwrap()
}

fn read_doc_depth(bytes: &[u8], max_any_depth: usize) -> Result<usize, ReadError> {
    let doc = ReadDoc::from_full_update_v1_with_limits(
        bytes.to_vec(),
        ReadLimits {
            max_any_depth,
            ..Default::default()
        },
    )?;
    let value = doc
        .map("root")
        .unwrap()
        .get("deep")
        .unwrap()
        .as_any()
        .unwrap()
        .to_owned();
    Ok(depth_of(&value).unwrap())
}

fn is_depth_error(result: Result<Update, JwstCodecError>) -> bool {
    matches!(result, Err(JwstCodecError::IncompleteDocument(message)) if message.contains("Any nesting depth"))
}

fn is_read_depth_error(result: Result<usize, ReadError>) -> bool {
    matches!(result, Err(ReadError::ResourceLimit("Any nesting depth")))
}

#[test]
fn external_crates_move_values_out_of_any() {
    if let Any::String(s) = Any::from("text") {
        let _: String = s;
    } else {
        unreachable!();
    }
    if let Any::Object(m) = Any::from(AHashMap::from_iter([("k".to_string(), Any::Null)])) {
        let _: AHashMap<String, Any> = *m;
    } else {
        unreachable!();
    }
    if let Any::Array(v) = Any::Array(vec![Any::True]) {
        let _: Vec<Any> = v;
    } else {
        unreachable!();
    }
    if let Any::Binary(b) = Any::from(vec![1u8, 2]) {
        let _: Vec<u8> = b;
    } else {
        unreachable!();
    }
}

/// Checks `bytes`, holding `root.deep` nested `depth` arrays deep, against
/// the default and the raised limits, and returns the re-encoded update.
fn check_trusted_paths(bytes: &[u8], depth: usize) -> Vec<u8> {
    // default entry points reject it
    assert!(matches!(
        doc(1).apply_update_from_binary_v1(bytes),
        Err(JwstCodecError::IncompleteDocument(_))
    ));
    assert!(is_depth_error(Update::decode_v1(bytes)));
    assert!(matches!(
        ReadDoc::from_full_update_v1(bytes.to_vec()),
        Err(ReadError::ResourceLimit("Any nesting depth"))
    ));

    // trusted entry points accept it
    let mut doc = doc(1);
    doc.apply_update(Update::decode_v1_with_max_any_depth(bytes, 256).unwrap())
        .unwrap();
    let value = doc
        .get_or_create_map("root")
        .unwrap()
        .get("deep")
        .unwrap()
        .to_any()
        .unwrap();
    assert_eq!(depth_of(&value), Some(depth));
    assert_eq!(value, nested(depth));
    assert!(doc.encode_update().is_ok());
    let encoded = doc.encode_update_v1().unwrap();
    assert_eq!(read_doc_depth(bytes, 256).unwrap(), depth);
    assert_eq!(read_doc_depth(&encoded, 256).unwrap(), depth);
    encoded
}

#[test]
#[cfg_attr(miri, ignore)]
fn trusted_paths_read_deep_any() {
    let bytes = update_with(nested(200));
    let encoded = check_trusted_paths(&bytes, 200);
    assert_eq!(encoded, bytes);
}

#[test]
fn trusted_paths_read_deep_any_under_miri() {
    // small enough for Miri, still deeper than a limit of 8
    let bytes = update_with(nested(12));
    assert!(is_depth_error(Update::decode_v1_with_max_any_depth(&bytes, 8)));
    assert!(is_read_depth_error(read_doc_depth(&bytes, 8)));
    let mut doc = doc(1);
    doc.apply_update(Update::decode_v1_with_max_any_depth(&bytes, 13).unwrap())
        .unwrap();
    assert_eq!(doc.encode_update_v1().unwrap(), bytes);
    assert_eq!(read_doc_depth(&bytes, 13).unwrap(), 12);
}

#[test]
fn zero_depth_limit_agrees_across_entry_points() {
    let any_at_zero = |bytes: &[u8]| Any::read_with_max_depth(&mut RawDecoder::new(bytes), 0);
    let encode = |value: &Any| {
        let mut encoder = RawEncoder::default();
        value.write(&mut encoder).unwrap();
        encoder.into_inner()
    };
    for (value, accepted) in [
        (Any::Integer(1), true),
        (Any::Array(Vec::new()), true),
        (Any::Object(Box::default()), true),
        (Any::Array(vec![Any::Null]), false),
        (
            Any::Object(Box::new(AHashMap::from_iter([("k".to_string(), Any::Null)]))),
            false,
        ),
    ] {
        assert_eq!(any_at_zero(&encode(&value)).is_ok(), accepted, "{value:?}");
        let bytes = update_with(value.clone());
        let update = Update::decode_v1_with_max_any_depth(&bytes, 0);
        let read = ReadDoc::from_full_update_v1_with_limits(
            bytes.clone(),
            ReadLimits {
                max_any_depth: 0,
                ..Default::default()
            },
        );
        if accepted {
            assert!(update.is_ok(), "{value:?}");
            assert!(read.is_ok(), "{value:?}");
        } else {
            assert!(is_depth_error(update), "{value:?}");
            assert!(
                matches!(read, Err(ReadError::ResourceLimit("Any nesting depth"))),
                "{value:?}"
            );
        }
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn limits_stop_at_the_configurable_maximum() {
    // `nested(n)` puts the leaf integer n + 1 levels deep
    let max = Any::MAX_CONFIGURABLE_DEPTH;
    let at_max = update_with(nested(max - 1));
    let beyond = update_with(nested(max));
    for limit in [max, max + 1, usize::MAX] {
        let mut doc = doc(1);
        doc.apply_update(Update::decode_v1_with_max_any_depth(&at_max, limit).unwrap())
            .unwrap();
        assert!(doc.encode_update().is_ok());
        assert_eq!(read_doc_depth(&at_max, limit).unwrap(), max - 1);

        assert!(is_depth_error(Update::decode_v1_with_max_any_depth(&beyond, limit)));
        assert!(is_read_depth_error(read_doc_depth(&beyond, limit)));
    }
}

/// Yjs 13.6.33 writes the nested value and reads back what y-octo encodes.
#[test]
#[ignore = "requires Node.js and the pinned oracle packages"]
fn online_deep_any_yjs_roundtrip() {
    use std::{
        io::Write,
        process::{Command, Stdio},
    };
    const DEPTH: usize = 200;
    let script = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/oracle/deep-any.mjs");
    let output = Command::new("node")
        .args([script, "--generate", &DEPTH.to_string()])
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    let hex = String::from_utf8(output.stdout).unwrap();
    let bytes: Vec<u8> = (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
        .collect();

    let encoded = check_trusted_paths(&bytes, DEPTH);
    assert_eq!(encoded, bytes);

    let mut child = Command::new("node")
        .args([script, "--verify", &DEPTH.to_string()])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let hex: String = encoded.iter().map(|byte| format!("{byte:02x}")).collect();
    child.stdin.take().unwrap().write_all(hex.as_bytes()).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        r#"{"depth":200,"leaf":42}"#
    );
}
