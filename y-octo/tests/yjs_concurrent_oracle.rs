mod support;

use serde_json::{Value as Json, json};
use support::{
    concurrent::{assert_snapshot as check_snapshot, fixtures as corpus},
    *,
};

#[test]
#[cfg_attr(miri, ignore = "Large semantic oracle; ordinary tests cover it")]
fn yjs_concurrent_updates_match_every_arrival() {
    let corpus = corpus();
    assert_provenance(&corpus);
    for scenario in corpus["records"].as_array().unwrap() {
        for plan in scenario["plans"].as_array().unwrap() {
            let mut d = doc(303, scenario["gc"].as_bool().unwrap());
            for (i, step) in plan["steps"].as_array().unwrap().iter().enumerate() {
                if let Some(index) = step["update"].as_u64() {
                    d.apply_update_from_binary_v1(bytes(&scenario["updates"][index as usize]))
                        .unwrap();
                }
                let context = format!(
                    "{} versions={} {} step {i}",
                    scenario["name"], scenario["versions"], plan["label"]
                );
                check_snapshot(&d, &step["expected"], &context);
                if let Some(pending) = step["pending"].as_bool() {
                    assert_eq!(d.has_pending_updates(), pending, "{context}");
                }
            }
        }
        if let Some(checkpoint) = scenario.get("bug_checkpoint") {
            let mut fresh = doc(404, true);
            fresh.apply_update_from_binary_v1(bytes(&checkpoint["update"])).unwrap();
            check_snapshot(&fresh, &checkpoint["remote"], "#757 first undo full update");
        }
        if let Some(full) = scenario.get("final_update") {
            let mut fresh = doc(404, true);
            fresh.apply_update_from_binary_v1(bytes(full)).unwrap();
            check_snapshot(&fresh, &scenario["final_remote"], "#757 full update remote state");
        }
    }
}

#[test]
#[cfg_attr(miri, ignore = "Large semantic oracle; ordinary tests cover it")]
fn nested_map_757_records_old_divergence_and_current_fix() {
    let corpus = corpus();
    assert_eq!(corpus["authoritative_version"], "13.6.33");
    assert!(
        corpus["version_differences"]
            .as_array()
            .unwrap()
            .contains(&json!("undo-nested-map-757"))
    );
    let find = |version: &str| {
        for_version(&corpus, version)
            .into_iter()
            .find(|s| s["name"] == "undo-nested-map-757")
            .unwrap()
    };
    let old = find("13.6.21");
    let current = find("13.6.33");
    assert_eq!(
        old["bug_checkpoint"]["author"]["map"],
        json!({"parent":{"type":"button","test":true}})
    );
    assert_eq!(old["bug_checkpoint"]["remote"]["map"], json!({"parent":{"test":true}}));
    assert_eq!(current["bug_checkpoint"]["author"], current["bug_checkpoint"]["remote"]);
    assert_eq!(
        current["bug_checkpoint"]["remote"]["map"],
        old["bug_checkpoint"]["author"]["map"]
    );
}

#[test]
#[cfg_attr(miri, ignore = "Large semantic oracle; ordinary tests cover it")]
fn relative_position_vectors_cover_missing_deleted_and_utf16_targets() {
    let corpus = corpus();
    let scenario = for_version(&corpus, "13.6.33")
        .into_iter()
        .find(|s| s["name"] == "relative-positions")
        .unwrap();
    assert_eq!(scenario["positions"].as_array().unwrap().len(), 30);
    // Each position starts unresolved on a new recipient, including nested
    // structures that have not arrived. The same encoded bytes are used at all
    // checkpoints; consumers can plug in the RelativePosition API
    // independently.
    for plan in scenario["plans"].as_array().unwrap() {
        assert!(
            plan["steps"][0]["positions"]
                .as_array()
                .unwrap()
                .iter()
                .any(Json::is_null)
        );
        let final_step = plan["steps"].as_array().unwrap().last().unwrap();
        assert!(
            final_step["positions"]
                .as_array()
                .unwrap()
                .iter()
                .any(|p| p["parent_deleted"] == true || p.is_null())
        );
    }
    for p in scenario["positions"].as_array().unwrap() {
        assert!(!bytes(&p["binary"]).is_empty());
    }
}

#[test]
#[cfg_attr(miri, ignore = "Large semantic oracle; ordinary tests cover it")]
fn retained_parent_positions_record_the_intentional_yjs_difference() {
    let corpus = corpus();
    let s = for_version(&corpus, "13.6.33")
        .into_iter()
        .find(|s| s["name"] == "relative-positions-retained-parent")
        .unwrap();
    let positions = s["plans"][0]["steps"].as_array().unwrap().last().unwrap()["positions"]
        .as_array()
        .unwrap();
    // Yjs resolves anchors in a deleted, retained nested type to index zero.
    // The agreed Rust API deliberately returns None for a deleted parent;
    // future anchor tests must assert that policy separately from this oracle.
    assert!(positions.iter().any(|p| p["parent_deleted"] == true && p["index"] == 0));
    let undo = for_version(&corpus, "13.6.33")
        .into_iter()
        .find(|s| s["name"] == "undo-concurrent-text")
        .unwrap();
    let after_undo = undo["actions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|a| a["label"] == "A undo preserves B")
        .unwrap();
    assert_eq!(after_undo["expected_author"]["text"], "内");
}

// Small lifetime paths extracted from the Yjs oracle; no gzip parsing in Miri.
#[cfg(miri)]
mod miri_smoke {
    use super::*;

    #[test]
    fn nested_parent_pending_gc_and_duplicate_apply() {
        // nested-create-delete-parent / arrival-1: deletion and child edit
        // precede their parent; repair/integrate then GC, followed by repeats.
        let updates = [
            "010965002701036d617006706172656e740127006500047465787402040065010a6e6573746564f09f988027006500056172726179000800650a037d017601066f706171756578750177017827006500036d6170012800650e036b657901770576616c756507010561727261790128006510036b65790177077369626c696e6700",
            "0102ca01004465020142a8650f01770672656d6f74650165020c010f01",
            "0002ca010100026502000c0d02",
        ];
        let mut d = doc(303, true);
        for (step, index) in [2, 1, 0, 1, 2].into_iter().enumerate() {
            d.apply_update_from_binary_v1(bytes(&json!(updates[index]))).unwrap();
            assert_eq!(d.has_pending_updates(), step < 2, "step {step}");
            assert!(d.get_or_create_map("map").unwrap().is_empty());
            let expected = if step < 2 {
                json!([])
            } else {
                json!([{"key":"sibling"}])
            };
            assert_eq!(
                serde_json::to_value(d.get_or_create_array("array").unwrap()).unwrap(),
                expected,
                "step {step}"
            );
            assert!(d.get_or_create_text("text").unwrap().to_delta().is_empty());
        }
    }

    #[test]
    fn overlapping_text_reverse_and_duplicate_apply() {
        // concurrent-text-overlap: all dependency updates arrive in reverse.
        let updates = [
            "010165000401047465787402787900",
            "0101ca0100c46500650103e5868500",
            "0002ca0101000165010001",
            "0002ca0101000165010101",
        ];
        let mut d = doc(303, true);
        for (step, index) in [3, 2, 1, 0, 3, 2, 1, 0].into_iter().enumerate() {
            d.apply_update_from_binary_v1(bytes(&json!(updates[index]))).unwrap();
            assert_eq!(d.has_pending_updates(), step < 3, "step {step}");
            let text = d.get_or_create_text("text").unwrap();
            assert!(text.to_string().is_empty());
            assert!(text.to_delta().is_empty());
        }
    }
}
