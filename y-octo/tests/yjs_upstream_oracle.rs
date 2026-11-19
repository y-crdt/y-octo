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
