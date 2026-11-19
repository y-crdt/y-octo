use std::{
    collections::{BTreeMap, BTreeSet},
    io::Write,
};

use serde_json::{Value as Json, json};
use y_octo::DocOptions;

use super::{digest::digest, trace};

pub const SMALL_CASES: [&str; 6] = [
    "updates.tests.js:testKeyEncoding",
    "snapshot.tests.js:testRestoreSnapshotWithSubType",
    "undo-redo.tests.js:testConsecutiveRedoBug",
    "y-text.tests.js:testFalsyFormats",
    "y-text.tests.js:testSplitSurrogateCharacter",
    "y-text.tests.js:testTypesAsEmbed",
];
pub fn read_gzip(input: &[u8]) -> Json {
    use std::io::Read;
    let mut text = String::new();
    flate2::read::GzDecoder::new(input).read_to_string(&mut text).unwrap();
    serde_json::from_str(&text).unwrap()
}
pub fn expand_manifest(input: &Json) -> Json {
    let mut out = input.clone();
    let digests = out.as_object_mut().unwrap().remove("digests").unwrap();
    let documents = out.as_object_mut().unwrap().remove("documents").unwrap();
    let documents: Vec<_> = documents
        .as_array()
        .unwrap()
        .iter()
        .map(|doc| {
            let mut doc = doc.clone();
            for (k, v) in doc.as_object_mut().unwrap() {
                if k.ends_with("_digest") {
                    *v = digests[v.as_u64().unwrap() as usize].clone();
                }
            }
            doc
        })
        .collect();
    for record in out["records"].as_array_mut().unwrap() {
        if let Some(docs) = record["docs"].as_array_mut() {
            for d in docs {
                *d = documents[d.as_u64().unwrap() as usize].clone();
            }
        }
    }
    out
}
fn state_hash(corpus: &Json, index: &Json, cache: &mut BTreeMap<usize, String>) -> String {
    let i = index.as_u64().unwrap() as usize;
    cache.entry(i).or_insert_with(|| digest(&corpus["states"][i])).clone()
}
/// Recompute provenance from the actual corpus, so removing a case/packet or
/// replacing an expected state cannot leave a stale embedded manifest valid.
pub fn summarize(corpus: &Json) -> Json {
    let mut out = corpus.clone();
    out.as_object_mut().unwrap().remove("updates");
    out.as_object_mut().unwrap().remove("states");
    out["digest_encoding"] = json!("tagged-json-sha256-v1");
    let mut hashes = BTreeMap::new();
    for record in out["records"].as_array_mut().unwrap() {
        if let Some(docs) = record["docs"].as_array_mut() {
            for d in docs {
                if let Some(i) = d.as_object_mut().unwrap().remove("native_update") {
                    d["native_update_digest"] = json!(digest(&corpus["updates"][i.as_u64().unwrap() as usize]));
                }
                let ids = d.as_object_mut().unwrap().remove("updates").unwrap();
                let packets: Vec<_> = ids
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|i| corpus["updates"][i.as_u64().unwrap() as usize].clone())
                    .collect();
                d["update_count"] = json!(packets.len());
                d["updates_digest"] = json!(digest(&json!(packets)));
                for (source, target) in [
                    ("expected", "expected_digest"),
                    ("available", "available_digest"),
                    ("native_end", "native_end_digest"),
                ] {
                    if let Some(i) = d.as_object_mut().unwrap().remove(source) {
                        d[target] = json!(state_hash(corpus, &i, &mut hashes));
                    }
                }
            }
        }
    }
    out
}
pub fn validate_manifest(corpus: &Json, small: bool) -> Result<Json, String> {
    let checked = read_gzip(include_bytes!("../oracle/upstream-manifest.json.gz"));
    let mut expected = expand_manifest(&checked);
    if small {
        expected["records"]
            .as_array_mut()
            .unwrap()
            .retain(|r| SMALL_CASES.contains(&r["name"].as_str().unwrap()));
        let found: BTreeSet<_> = corpus["records"]
            .as_array()
            .unwrap()
            .iter()
            .map(|r| r["name"].as_str().unwrap())
            .collect();
        if found != SMALL_CASES.into_iter().collect() {
            return Err("manifest mismatch: missing/unexpected small semantic case".into());
        }
    }
    let actual = summarize(corpus);
    if actual != expected {
        return Err(format!(
            "manifest mismatch: case inventory, stream or expected digest changed; actual={} expected={}",
            digest(&actual),
            digest(&expected)
        ));
    }
    Ok(expected)
}
fn known_for<'a>(known: &'a Json, name: &str, index: usize, versions: &Json) -> Option<&'a Json> {
    known["cases"].as_array().unwrap().iter().find(|r| {
        r["case"] == name
            && r["versions"] == *versions
            && r["replica_ranges"].as_array().unwrap().iter().any(|r| {
                let start = r[0].as_u64().unwrap() as usize;
                let n = r[1].as_u64().unwrap() as usize;
                (start..start + n).contains(&index)
            })
    })
}
pub fn replay(corpus: &Json, small: bool, exports: &std::path::Path) -> Result<(usize, usize, usize), String> {
    let expected_manifest = validate_manifest(corpus, small)?;
    let known: Json = serde_json::from_str(include_str!("../oracle/upstream-known-failures.json")).unwrap();
    let mut export_file = std::fs::File::create(exports).map_err(|e| e.to_string())?;
    let mut failures = Vec::new();
    let (mut cases, mut docs, mut matched) = (0, 0, 0);
    for (record, checked) in corpus["records"]
        .as_array()
        .unwrap()
        .iter()
        .zip(expected_manifest["records"].as_array().unwrap())
    {
        if !matches!(record["status"].as_str(), Some("recorded" | "no_updates")) {
            continue;
        }
        cases += 1;
        println!(
            "REPLAY {} docs={}",
            record["name"],
            record["docs"].as_array().unwrap().len()
        );
        for (index, meta) in record["docs"].as_array().unwrap().iter().enumerate() {
            docs += 1;
            let full_expected = &corpus["states"][meta["expected"].as_u64().unwrap() as usize];
            let mut clients: Vec<_> = full_expected["sv"]
                .as_array()
                .unwrap()
                .iter()
                .map(|v| v[0].clone())
                .collect();
            clients.extend(full_expected["ds"].as_array().unwrap().iter().map(|v| v[0].clone()));
            let input = json!({"replicas":clients,"roots":meta["roots"]});
            let known = known_for(&known, record["name"].as_str().unwrap(), index, &record["versions"]);
            let result = (|| -> Result<bool, String> {
                let mut doc = DocOptions {
                    client_id: 800000,
                    guid: "upstream-replay".into(),
                    gc: meta["gc"].as_bool().unwrap(),
                }
                .build();
                for (name, kind) in meta["roots"].as_object().unwrap() {
                    match kind.as_str().unwrap() {
                        "text" => {
                            doc.get_or_create_text(name).map_err(|e| e.to_string())?;
                        }
                        "array" => {
                            doc.get_or_create_array(name).map_err(|e| e.to_string())?;
                        }
                        "map" => {
                            doc.get_or_create_map(name).map_err(|e| e.to_string())?;
                        }
                        k => return Err(format!("unsupported root {k}")),
                    }
                }
                for (step, u) in meta["updates"].as_array().unwrap().iter().enumerate() {
                    doc.apply_update_from_binary_v1(super::bytes(&corpus["updates"][u.as_u64().unwrap() as usize]))
                        .map_err(|e| format!("apply packet {step}: {e}"))?;
                }
                if let Some(index) = meta.get("native_update") {
                    let native_expected = &corpus["states"][meta["native_end"].as_u64().unwrap() as usize];
                    let mut native_clients: Vec<_> = native_expected["sv"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|v| v[0].clone())
                        .collect();
                    native_clients.extend(native_expected["ds"].as_array().unwrap().iter().map(|v| v[0].clone()));
                    let native_schema = json!({"replicas":native_clients,"roots":meta["roots"]});
                    let mut native = DocOptions {
                        client_id: 800001,
                        guid: "upstream-native-checkpoint".into(),
                        gc: meta["gc"].as_bool().unwrap(),
                    }
                    .build();
                    native
                        .apply_update_from_binary_v1(super::bytes(&corpus["updates"][index.as_u64().unwrap() as usize]))
                        .map_err(|e| format!("native checkpoint apply: {e}"))?;
                    let native = trace::snapshot(&native, &native_schema)?;
                    if digest(&native) != digest(native_expected) {
                        return Err(format!(
                            "native checkpoint state mismatch: {} != {}",
                            digest(&native),
                            digest(native_expected)
                        ));
                    }
                }
                for (name, length) in meta["text_lengths"].as_object().unwrap() {
                    let actual = doc.get_or_create_text(name).map_err(|e| e.to_string())?.len();
                    if actual != length.as_u64().unwrap() {
                        return Err(format!("text length mismatch at {name}: {actual} != {length}"));
                    }
                }
                let checked = &checked["docs"][index];
                match trace::snapshot(&doc, &input) {
                    Ok(actual) => {
                        if known.is_some() {
                            return Err("known identity_runs failure unexpectedly passed".into());
                        }
                        if digest(&actual) != checked["expected_digest"].as_str().unwrap() {
                            return Err(format!(
                                "state digest mismatch: actual={} expected={}",
                                digest(&actual),
                                checked["expected_digest"]
                            ));
                        }
                        Ok(false)
                    }
                    Err(error) => {
                        let known = known.ok_or_else(|| format!("unregistered projection error: {error}"))?;
                        if known["stage"] != "identity_runs" || known["error"] != error {
                            return Err(format!("different error/stage: {error}"));
                        }
                        let (actual, missing) = trace::snapshot_available(&doc, &input)?;
                        let paths: Vec<_> = missing.iter().map(|(p, _)| p.clone()).collect();
                        if json!(paths) != known["missing_text_paths"]
                            || json!(paths) != meta["missing_text_paths"]
                            || missing.iter().any(|(_, e)| *e != error)
                        {
                            return Err(format!("different missing fields: {missing:?}"));
                        }
                        if digest(&actual) != checked["available_digest"].as_str().unwrap() {
                            return Err(format!(
                                "available-field digest mismatch: actual={} expected={}",
                                digest(&actual),
                                checked["available_digest"]
                            ));
                        }
                        let full = doc.encode_update_v1().map_err(|e| format!("export: {e}"))?;
                        // A second Yjs pass verifies full exported content,
                        // including shared embeds unavailable to current
                        // live/frozen readers.
                        let frozen = y_octo::ReadDoc::from_full_update_v1(full.clone())
                            .map_err(|e| format!("frozen decode: {e}"))?;
                        for (name, length) in meta["text_lengths"].as_object().unwrap() {
                            let frozen = frozen.text(name).ok_or_else(|| format!("missing frozen text {name}"))?;
                            let live = doc.get_or_create_text(name).map_err(|e| e.to_string())?;
                            if frozen.len() != length.as_u64().unwrap()
                                || frozen.to_string() != live.to_string()
                                || frozen.to_delta() != live.to_delta()
                            {
                                return Err(format!("frozen available text mismatch at {name}"));
                            }
                        }
                        let line = json!({"case":record["name"],"replica":index,"versions":record["versions"],"roots":meta["roots"],"gc":meta["gc"],"update":trace::encode_hex(&full),"expected_digest":checked["expected_digest"]});
                        writeln!(export_file, "{line}").map_err(|e| e.to_string())?;
                        Ok(true)
                    }
                }
            })();
            match result {
                Ok(true) => matched += 1,
                Ok(false) => {}
                Err(error) => failures.push(format!(
                    "{} versions={} replica={index}: {error}",
                    record["name"], record["versions"]
                )),
            }
        }
    }
    println!(
        "upstream cases={cases} docs={docs} exact_known_failures={matched} unexpected={}",
        failures.len()
    );
    if failures.is_empty() {
        Ok((cases, docs, matched))
    } else {
        Err(failures.join("\n"))
    }
}
