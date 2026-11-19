//! Check that compacted updates can be reopened and edited.
use serde_json::{Value as Json, json};

use super::trace::{self, ReplicaSet, online::Oracle};
type Result<T> = std::result::Result<T, String>;

fn compact(updates: &[String]) -> Result<Vec<u8>> {
    y_octo::merge_updates_v1(updates.iter().map(|u| trace::decode_hex(u)))
        .and_then(|update| update.encode_v1())
        .map_err(|e| e.to_string())
}
fn arrivals(updates: &[String], order: usize) -> Vec<String> {
    let mut packets = updates.to_vec();
    match order {
        1 => packets.reverse(),
        2 => packets.rotate_left(1),
        _ => {}
    }
    packets.extend(packets.clone());
    packets
}
fn wire(oracle: &mut Oracle, expected: &[String], actual: &[u8], phase: &str, evidence: &mut Json) -> Result<String> {
    let request = json!({"kind":"storage_wire","updates":expected,"actual":trace::encode_hex(actual)});
    evidence["phase"] = json!(phase);
    evidence["wire_request"] = request.clone();
    let result = oracle.command(request)?;
    if result["actual"] != result["expected"] {
        evidence["wire_result"] = result;
        return Err(format!(
            "{phase}: normalized raw structs/origins/parent/content or DS differ"
        ));
    }
    Ok(result["merged"].as_str().unwrap().to_owned())
}
fn state(native: &ReplicaSet, at: usize, expected: &Json, schema: &Json, phase: &str) -> Result<()> {
    let actual = trace::snapshot(&native.docs[at], schema)?;
    if actual != *expected {
        return Err(format!("{phase}: snapshot mismatch\nRust={actual}\nYjs={expected}"));
    }
    Ok(())
}
fn apply(at: usize, update: &str) -> Json {
    json!({"op":"apply","at":at,"update":update})
}

fn chain(oracle: &mut Oracle, version: &str, gc: bool, evidence: &mut Json) -> Result<()> {
    // Every author in the stored updates is included in the trace's DS ceiling.
    // A different native identity is used for each reopened editing session.
    let schema = json!({"schema":1,"name":"three-round-storage-chain","gc":gc,
        "replicas":[303,304,305,401,402,403,101,202,701,702],
        "roots":{"text":"text","array":"array","map":"map"}});
    let reset = json!({"kind":"reset","version":version,"trace":schema});
    oracle.command(reset.clone())?;
    let seed = oracle.command(json!({"kind":"storage_seed"}))?;
    evidence["seed"] = seed.clone();

    let control = vec![
        seed["base"].as_str().unwrap().to_owned(),
        seed["parent_deletion"].as_str().unwrap().to_owned(),
    ];
    wire(oracle, &control, &compact(&control)?, "raw-control", evidence)?;
    if gc {
        let collected = oracle.command(json!({"kind":"storage_wire","updates":control,"actual":seed["collected"]}))?;
        if collected["actual"] == collected["expected"] {
            return Err("normalizer missed the apply/GC/export substitution for raw compaction".into());
        }
    }
    let mut stored = seed["base"].as_str().unwrap().to_owned();
    let mut reference = stored.clone();
    for round in 0..3 {
        evidence["round"] = json!(round);
        oracle.command(reset.clone())?;
        let mut rust_packets = vec![stored];
        let mut yjs_packets = vec![reference];
        for name in match round {
            0 => vec!["child", "deletion"],
            1 => vec!["parent"],
            _ => vec![],
        } {
            let packet = seed[name].as_str().unwrap().to_owned();
            rust_packets.push(packet.clone());
            yjs_packets.push(packet);
        }
        let before_remote = wire(
            oracle,
            &yjs_packets,
            &compact(&rust_packets)?,
            "before-remote",
            evidence,
        )?;
        let remote = round + 3;
        oracle.command(json!({"kind":"step","step":apply(remote, &before_remote)}))?;
        for step in [
            json!({"op":"array_insert","at":remote,"target":["array"],"index":"end","value":{"remote":round}}),
            json!({"op":"map_insert","at":remote,"target":["map"],"key":"peer","value":round}),
        ] {
            let result = oracle.command(json!({"kind":"step","step":step}))?;
            let packet = result["update"].as_str().unwrap().to_owned();
            rust_packets.push(packet.clone());
            yjs_packets.push(packet);
        }
        let mut candidates = Vec::new();
        for order in 0..3 {
            let merged = compact(&arrivals(&rust_packets, order))?;
            let expected = wire(
                oracle,
                &arrivals(&yjs_packets, order),
                &merged,
                &format!("round-{round}/arrival-{order}"),
                evidence,
            )?;
            candidates.push((merged, expected));
        }
        let (merged, expected) = candidates.swap_remove(round);
        evidence["phase"] = json!("load");
        evidence["load"] = json!({"rust":trace::encode_hex(&merged),"yjs":expected});
        let mut native = ReplicaSet::new(&schema)?;
        native.step(&apply(round, &trace::encode_hex(&merged)))?;
        let mut result = oracle.command(json!({"kind":"step","step":apply(round, &expected)}))?;
        state(&native, round, &result["snapshots"][round], &schema, "load")?;
        if native.docs[round].has_pending_updates() != (round == 0) {
            return Err(format!(
                "round {round}: pending should survive the first reopen, then resolve"
            ));
        }
        let mut steps = vec![
            json!({"op":"map_insert","at":round,"target":["map"],"key":"round","value":round}),
            json!({"op":"array_insert","at":round,"target":["array"],"index":"middle","value":[round,{"opaque":true}]}),
            json!({"op":"text_insert","at":round,"target":["map","keep","text"],"index":"end","value":format!("/native-{round}😀")}),
        ];
        if round == 2 {
            steps.push(json!({"op":"map_remove","at":round,"target":["map"],"key":"discard"}));
        }
        for step in steps {
            evidence["phase"] = json!("edit");
            evidence["step"] = step.clone();
            native.step(&step)?;
            result = oracle.command(json!({"kind":"step","step":step}))?;
            state(&native, round, &result["snapshots"][round], &schema, "edit")?;
        }
        let full = native.docs[round].encode_update_v1().map_err(|e| e.to_string())?;
        let yjs_full = result["full"].as_str().unwrap().to_owned();
        wire(
            oracle,
            std::slice::from_ref(&yjs_full),
            &full,
            "edited-export-including-pending",
            evidence,
        )?;
        let persisted = compact(&[
            trace::encode_hex(&merged),
            trace::encode_hex(&full),
            trace::encode_hex(&full),
        ])?;
        reference = wire(
            oracle,
            &[expected, yjs_full.clone(), yjs_full],
            &persisted,
            "recompact",
            evidence,
        )?;
        stored = trace::encode_hex(&persisted);
        evidence["phase"] = json!("reopen-compacted");
        let mut reopened = ReplicaSet::new(&schema)?;
        reopened.step(&apply(8, &stored))?;
        let peer = oracle.command(json!({"kind":"step","step":apply(8, &reference)}))?;
        state(&reopened, 8, &peer["snapshots"][8], &schema, "reopen-compacted")?;
        println!(
            "storage Yjs={version} gc={gc} round={} pending={} arrival_orders=3",
            round + 1,
            reopened.docs[8].has_pending_updates()
        );
    }
    // Continue with one actual Rust writer and one actual Yjs writer. Each
    // consumes the other engine's bytes before the next pair of local edits.
    evidence["phase"] = json!("future-bidirectional");
    evidence["future_start"] = json!(stored);
    evidence["future_exchanges"] = json!([]);
    oracle.command(reset)?;
    let mut pair = ReplicaSet::new(&schema)?;
    pair.step(&apply(8, &stored))?;
    oracle.command(json!({"kind":"step","step":apply(9, &stored)}))?;
    let edits = [
        (
            json!({"op":"text_insert","at":8,"target":["map","keep","text"],"index":"begin","value":"native-future/"}),
            json!({"op":"array_insert","at":9,"target":["array"],"index":"end","value":{"peer_future":true}}),
        ),
        (
            json!({"op":"map_insert","at":8,"target":["map","later"],"key":"same","value":"native"}),
            json!({"op":"map_insert","at":9,"target":["map","later"],"key":"same","value":"Yjs"}),
        ),
        (
            json!({"op":"array_remove","at":8,"target":["array"],"index":"middle","length":2}),
            json!({"op":"text_insert","at":9,"target":["text"],"index":"end","value":"/peer-future😀"}),
        ),
    ];
    for (turn, (rust_edit, yjs_edit)) in edits.into_iter().enumerate() {
        let before = pair.docs[8].get_state_vector();
        pair.step(&rust_edit)?;
        let rust_update = pair.docs[8]
            .encode_state_as_update_v1(&before)
            .map_err(|e| e.to_string())?;
        let remote = oracle.command(json!({"kind":"step","step":yjs_edit}))?;
        let yjs_update = remote["update"].as_str().unwrap();
        evidence["future_exchanges"].as_array_mut().unwrap().push(json!({"turn":turn,"rust_edit":rust_edit,"yjs_edit":yjs_edit,"rust_update":trace::encode_hex(&rust_update),"yjs_update":yjs_update}));
        pair.step(&apply(8, yjs_update))?;
        let received = oracle.command(json!({"kind":"step","step":apply(9, &trace::encode_hex(&rust_update))}))?;
        state(
            &pair,
            8,
            &received["snapshots"][9],
            &schema,
            &format!("future turn {turn}: incremental delivery"),
        )?;
        // Also exchange any formatting-maintenance deletes derived by apply,
        // as in the existing differential harness's causal-mirror closure.
        pair.step(&apply(8, received["full"].as_str().unwrap()))?;
        let full = pair.docs[8].encode_update_v1().map_err(|e| e.to_string())?;
        let echoed = oracle.command(json!({"kind":"step","step":apply(9, &trace::encode_hex(&full))}))?;
        pair.step(&apply(8, echoed["full"].as_str().unwrap()))?;
        state(
            &pair,
            8,
            &echoed["snapshots"][9],
            &schema,
            "future mixed-engine writers",
        )?;
        if pair.docs[8].has_pending_updates() {
            return Err(format!("future turn {turn}: pending updates remain"));
        }
    }
    println!("storage Yjs={version} gc={gc}: three future mixed-engine edit/exchange turns passed");
    Ok(())
}

pub fn verify(oracle: &mut Oracle, version: &str, gc: bool) -> Result<()> {
    let mut evidence = json!({"version":version,"gc":gc});
    if let Err(error) = chain(oracle, version, gc, &mut evidence) {
        evidence["error"] = json!(error);
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../target/trace-failures");
        std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
        let path = dir.join(format!("storage-{version}-gc-{gc}.json"));
        std::fs::write(&path, serde_json::to_vec_pretty(&evidence).unwrap()).map_err(|e| e.to_string())?;
        return Err(format!("{error}; storage checkpoint saved to {}", path.display()));
    }
    Ok(())
}
