mod support;
use support::upstream;

#[test]
#[cfg_attr(miri, ignore = "Semantic upstream vectors run in ordinary tests")]
fn upstream_semantic_vectors() {
    let corpus = upstream::read_gzip(include_bytes!("oracle/upstream-small.json.gz"));
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../target/yjs-oracle");
    std::fs::create_dir_all(&dir).unwrap();
    upstream::replay(&corpus, true, &dir.join("small-exports.jsonl")).unwrap();
}
#[test]
#[ignore = "Requires node tests/oracle/upstream.mjs --check in the dedicated CI job"]
fn replay_upstream_factory() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../target/yjs-oracle");
    let path = std::env::var_os("YJS_UPSTREAM_CORPUS")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| dir.join("upstream.json.gz"));
    let corpus = upstream::read_gzip(&std::fs::read(path).unwrap());
    std::fs::create_dir_all(&dir).unwrap();
    let result = upstream::replay(&corpus, false, &dir.join("known-exports.jsonl"));
    if let Err(error) = &result {
        std::fs::write(dir.join("failures.txt"), error).unwrap();
    }
    result.unwrap();
}

#[test]
#[cfg_attr(miri, ignore = "Manifest mutation checks run in ordinary tests")]
fn upstream_manifest_rejects_missing_case_and_changed_digest() {
    let original = upstream::read_gzip(include_bytes!("oracle/upstream-small.json.gz"));
    upstream::validate_manifest(&original, true).unwrap();
    let mut missing = original.clone();
    missing["records"].as_array_mut().unwrap().pop();
    let error = upstream::validate_manifest(&missing, true).unwrap_err();
    assert!(error.contains("missing/unexpected"), "{error}");
    let mut changed = original;
    changed["states"][0]["tampered"] = serde_json::json!(true);
    let error = upstream::validate_manifest(&changed, true).unwrap_err();
    assert!(error.contains("expected digest changed"), "{error}");
}

#[test]
#[cfg_attr(miri, ignore = "Projection classification checks run in ordinary tests")]
fn known_reader_gap_uses_typed_category_and_keeps_stage_and_paths() {
    use serde_json::json;
    use support::trace::{self, ProjectionError};
    use y_octo::JwstCodecError;

    let corpus = upstream::read_gzip(include_bytes!("oracle/upstream-small.json.gz"));
    let record = corpus["records"]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r["name"] == "y-text.tests.js:testTypesAsEmbed")
        .unwrap();
    let meta = &record["docs"][0];
    let mut doc = y_octo::DocOptions {
        client_id: 800000,
        gc: meta["gc"].as_bool().unwrap(),
        ..Default::default()
    }
    .build();
    doc.get_or_create_text("text").unwrap();
    for update in meta["updates"].as_array().unwrap() {
        doc.apply_update_from_binary_v1(support::bytes(&corpus["updates"][update.as_u64().unwrap() as usize]))
            .unwrap();
    }
    let state = &corpus["states"][meta["expected"].as_u64().unwrap() as usize];
    let schema = json!({"roots":meta["roots"],"replicas":state["sv"].as_array().unwrap().iter().map(|r|r[0].clone()).collect::<Vec<_>>()});
    let error = trace::snapshot_projection(&doc, &schema).unwrap_err();
    let (_, missing) = trace::snapshot_available(&doc, &schema).unwrap();
    let registry: serde_json::Value =
        serde_json::from_str(include_str!("oracle/upstream-known-failures.json")).unwrap();
    let known = registry["cases"]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r["case"] == record["name"])
        .unwrap();
    let check = |known: &serde_json::Value, error: &ProjectionError, missing: &[ProjectionError]| {
        upstream::check_known_projection(known, error, missing, &meta["missing_text_paths"])
    };
    check(known, &error, &missing).unwrap();

    // Different human-readable details on the same variant must be accepted.
    let renamed = ProjectionError::IdentityRuns {
        path: "/roots/text".into(),
        source: JwstCodecError::InvalidStructType("new diagnostic wording"),
    };
    check(known, &renamed, &missing).unwrap();
    let other = ProjectionError::IdentityRuns {
        path: "/roots/text".into(),
        source: JwstCodecError::TypeCastError("text content"),
    };
    assert!(check(known, &other, &missing).is_err());
    assert!(check(known, &error, std::slice::from_ref(&other)).is_err());
    assert!(check(known, &ProjectionError::Other(error.to_string()), &missing).is_err());
    for (key, value) in [
        ("stage", json!("to_delta")),
        ("error_category", json!("TypeCastError")),
        ("missing_text_paths", json!(["/roots/other"])),
    ] {
        let mut changed = known.clone();
        changed[key] = value;
        assert!(check(&changed, &error, &missing).is_err(), "accepted changed {key}");
    }
}
