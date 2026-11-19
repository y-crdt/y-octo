mod support;
use serde_json::Value as Json;
use support::trace::{self, ReplicaSet, online::Oracle};

fn traces() -> Vec<Json> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/traces");
    let mut paths = std::fs::read_dir(dir)
        .unwrap()
        .map(|p| p.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "gz"))
        .collect::<Vec<_>>();
    paths.sort();
    paths
        .iter()
        .map(|path| {
            use std::io::Read;
            let mut json = String::new();
            flate2::read::GzDecoder::new(std::fs::File::open(path).unwrap())
                .read_to_string(&mut json)
                .unwrap();
            serde_json::from_str(&json).unwrap()
        })
        .collect()
}
fn run_offline(trace: &Json) -> Result<(), String> {
    if matches!(
        trace["check"]["kind"].as_str(),
        Some("update_properties" | "packet_apply")
    ) {
        trace::generate::replay(trace).map_err(|e| e.to_string())?;
    }
    let mut native = ReplicaSet::new(trace)?;
    for (i, step) in trace["steps"].as_array().unwrap().iter().enumerate() {
        native
            .step(step)
            .map_err(|e| format!("{} step {i}: {e}", trace["name"]))?;
    }
    for (i, d) in native.docs.iter().enumerate() {
        let got = trace::snapshot(d, trace)?;
        if trace::semantic(&got) != trace::semantic(&trace["expected"][i]) {
            return Err(format!(
                "{} replica {i}: {got} != {}",
                trace["name"], trace["expected"][i]
            ));
        }
        let mut fresh = ReplicaSet::mirror(trace)?;
        fresh[i]
            .apply_update_from_binary_v1(d.encode_update_v1().map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
        let reopened = trace::snapshot(&fresh[i], trace)?;
        if trace::semantic(&reopened) != trace::semantic(&got) {
            return Err(format!("{} reopen {i}: {reopened} != {got}", trace["name"]));
        }
    }
    Ok(())
}
#[test]
#[cfg_attr(
    miri,
    ignore = "Semantic traces run in ordinary tests; targeted Miri cases cover lifetimes"
)]
fn offline_regression_traces() {
    for trace in traces().iter().filter(|t| t["known_issue"].is_null()) {
        run_offline(trace).unwrap();
    }
}
#[test]
#[ignore = "A2: live remote Text marker invalidation"]
fn offline_text_marker_regression() {
    run_offline(
        &traces()
            .into_iter()
            .find(|t| t["name"] == "remote-marker-text")
            .unwrap(),
    )
    .unwrap();
}
#[test]
#[ignore = "A2: live remote Array marker invalidation"]
fn offline_array_marker_regression() {
    run_offline(
        &traces()
            .into_iter()
            .find(|t| t["name"] == "remote-marker-array")
            .unwrap(),
    )
    .unwrap();
}
#[test]
#[ignore = "Requires Node and npm ci --prefix y-octo/tests/oracle"]
fn online_yjs_differential() {
    let mut oracle = Oracle::start().unwrap();
    let mut failures = Vec::new();
    for version in ["13.6.21", "13.6.33"] {
        for trace in traces().iter().filter(|t| t["known_issue"].is_null()) {
            if matches!(
                trace["check"]["kind"].as_str(),
                Some("update_properties" | "packet_apply")
            ) && let Err(error) = trace::generate::replay(trace)
            {
                failures.push(error.to_string());
            }
            if (trace["versions"].is_null() || trace["versions"].as_array().unwrap().iter().any(|v| v == version))
                && let Err(error) = oracle.compare(trace, version)
            {
                failures.push(error.to_string());
            }
        }
    }
    for seed in 1..=32 {
        let trace = trace::generate::trace(seed);
        for version in ["13.6.21", "13.6.33"] {
            if let Err(error) = oracle.compare(&trace, version) {
                let minimal = trace::online::minimize(&mut oracle, &trace, version, &error);
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .parent()
                    .unwrap()
                    .join("target/trace-failures");
                std::fs::create_dir_all(&path).unwrap();
                let file = path.join(format!("random-{seed}-{version}.json"));
                let json = serde_json::to_string_pretty(&minimal).unwrap();
                std::fs::write(&file, &json).unwrap();
                failures.push(format!("{error}\nminimized trace saved to {}:\n{json}", file.display()));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
#[test]
#[ignore = "A2 Text marker bug; requires pinned Node oracle"]
fn online_text_marker_regression() {
    let mut oracle = Oracle::start().unwrap();
    let t = traces()
        .into_iter()
        .find(|t| t["name"] == "remote-marker-text")
        .unwrap();
    oracle.compare(&t, "13.6.33").unwrap();
}
#[test]
#[ignore = "A2 Array marker bug; requires pinned Node oracle"]
fn online_array_marker_regression() {
    let mut oracle = Oracle::start().unwrap();
    let t = traces()
        .into_iter()
        .find(|t| t["name"] == "remote-marker-array")
        .unwrap();
    oracle.compare(&t, "13.6.33").unwrap();
}

#[test]
#[cfg_attr(
    miri,
    ignore = "Seeded semantic properties run in ordinary tests; targeted Miri cases cover lifetimes"
)]
fn reference_free_update_properties() {
    let mut failures = Vec::new();
    for seed in 1..=32 {
        let trace = trace::generate::trace(seed);
        if let Err(error) = trace::generate::update_properties(&trace, seed) {
            let minimal = trace::generate::regression(&trace, &error, seed);
            failures.push(format!(
                "{error}\n{}",
                trace::save_failure(&minimal, &format!("property-{seed}"))
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

#[test]
#[ignore = "Explicit diagnostic: TRACE_INPUT points to a readable saved regression trace"]
fn replay_saved_trace() {
    let path = std::env::var("TRACE_INPUT").expect("set TRACE_INPUT to a saved JSON trace");
    let trace: Json = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    if matches!(
        trace["check"]["kind"].as_str(),
        Some("update_properties" | "packet_apply")
    ) {
        let result = trace::generate::replay(&trace);
        println!(
            "check={} seed={} expected_failure={} result={result:?}",
            trace["check"]["kind"], trace["check"]["seed"], trace["check"]["failure_kind"]
        );
        if let Err(error) = &result {
            assert_eq!(
                Some(error.kind),
                trace["check"]["failure_kind"].as_str(),
                "saved failure changed category"
            );
        }
        assert!(result.is_ok());
        return;
    }
    let mut oracle = Oracle::start().unwrap();
    let versions = trace["check"]["version"]
        .as_str()
        .map(|v| vec![v])
        .unwrap_or_else(|| vec!["13.6.21", "13.6.33"]);
    for version in versions {
        let result = oracle.compare(&trace, version);
        println!("{version}: {result:?}");
        if let Err(error) = &result
            && let Some(kind) = trace["check"]["failure_kind"].as_str()
        {
            assert_eq!(error.kind, kind, "saved failure changed category");
            assert_eq!(
                Some(error.direction),
                trace["check"]["direction"].as_str(),
                "saved failure changed direction"
            );
        }
        assert!(result.is_ok());
    }
}

#[test]
#[ignore = "Requires pinned Node oracle; focused Rust-to-Yjs map wire regression"]
fn online_map_gc_wire_regression() {
    let trace = traces().into_iter().find(|t| t["name"] == "map-gc-reinsert").unwrap();
    let mut oracle = Oracle::start().unwrap();
    for version in ["13.6.21", "13.6.33"] {
        oracle.compare(&trace, version).unwrap();
    }
}

#[test]
#[cfg_attr(miri, ignore = "Semantic UTF-16 boundary matrix runs in ordinary tests")]
fn arbitrary_state_vector_preserves_source() {
    // A synthetic state vector can end inside a surrogate pair. Unlike Yjs's
    // duplicate-struct repair side effect, encoding/echoing it preserves
    // source.
    for clock in 0..=5 {
        let trace = serde_json::json!({"replicas":[101,202],"roots":{"text":"text"}});
        let mut set = ReplicaSet::new(&trace).unwrap();
        let mut text = set.docs[0].get_or_create_text("text").unwrap();
        text.insert(0, "a😀b").unwrap();
        let original = set.docs[0].encode_update_v1().unwrap();
        let state = y_octo::StateVector::from([(101, clock)]);
        let tail = set.docs[0].encode_state_as_update_v1(&state).unwrap();
        assert_eq!(set.docs[0].encode_update_v1().unwrap(), original, "clock {clock}");
        set.docs[1].apply_update_from_binary_v1(tail).unwrap();
        let echo = set.docs[1].encode_update_v1().unwrap();
        set.docs[0].apply_update_from_binary_v1(echo).unwrap();
        assert_eq!(text.to_string(), "a😀b", "echo clock {clock}");
        assert_eq!(set.docs[0].encode_update_v1().unwrap(), original, "echo clock {clock}");
    }
}
