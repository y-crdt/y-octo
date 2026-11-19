use super::*;

/// Small, explicitly seeded generator; positions are symbolic so deleting
/// operations during shrinking does not manufacture out-of-range indices.
pub struct Random(u32);
impl Random {
    pub fn new(seed: u32) -> Self {
        Self(seed)
    }
    pub fn next(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 17;
        self.0 ^= self.0 << 5;
        self.0 as usize % n
    }
    pub fn shuffle<T>(&mut self, values: &mut [T]) {
        for i in (1..values.len()).rev() {
            let j = self.next(i + 1);
            values.swap(i, j);
        }
    }
}
pub fn trace(seed: u32) -> Json {
    let mut random = Random::new(seed);
    let mut steps = Vec::new();
    for at in 0..3 {
        steps.push(json!({"op":"create","at":at,"target":["map"],"key":"parent","kind":"map"}));
        for (key, kind) in [("t", "text"), ("a", "array"), ("m", "map")] {
            steps.push(json!({"op":"create","at":at,"target":["map","parent"],"key":key,"kind":kind}));
        }
    }
    for _ in 0..32 {
        let at = random.next(3);
        let pos = ["begin", "middle", "end"][random.next(3)];
        let nested = random.next(2) == 1;
        let key = ["k", "x", "y"][random.next(3)];
        let text = if nested {
            json!(["map", "parent", "t"])
        } else {
            json!(["text"])
        };
        let array = if nested {
            json!(["map", "parent", "a"])
        } else {
            json!(["array"])
        };
        let map = if nested {
            json!(["map", "parent", "m"])
        } else {
            json!(["map"])
        };
        let step = match random.next(10) {
            0 | 1 => {
                json!({"op":"text_insert","at":at,"target":text,"index":pos,"value":(["a","界","😀","NOP"][random.next(4)])})
            }
            2 => json!({"op":"text_remove","at":at,"target":text,"index":pos,"length":1+random.next(3)}),
            3 => {
                json!({"op":"array_insert","at":at,"target":array,"index":pos,"value":([json!(random.next(100)),json!(["x",true]),json!({"opaque":seed})][random.next(3)].clone())})
            }
            4 => json!({"op":"array_remove","at":at,"target":array,"index":pos,"length":1+random.next(2)}),
            5 => json!({"op":"map_insert","at":at,"target":map,"key":key,"value":random.next(100)}),
            6 => json!({"op":"map_remove","at":at,"target":map,"key":key}),
            7 => {
                json!({"op":"format","at":at,"target":text,"index":"begin","length":1+random.next(4),"attributes":{"bold":random.next(2)==1}})
            }
            8 => json!({"op":"text_embed","at":at,"target":text,"index":pos,"value":{"ref":random.next(10)}}),
            _ => json!({"op":"gc","at":at}),
        };
        steps.push(step);
    }
    // Batch sequence edits before delivering remote updates.
    for _ in 0..6 {
        let from = random.next(3);
        let to = (from + 1 + random.next(2)) % 3;
        steps.push(json!({"op":"sync","from":from,"to":to,"updates":"all","reverse":random.next(2)==1,"repeat":1+random.next(2)}));
    }
    for at in 0..3 {
        steps.push(json!({"op":"map_insert","at":at,"target":["map"],"key":"after-remote","value":at}));
    }
    for from in 0..3 {
        for to in 0..3 {
            if from != to {
                steps.push(json!({"op":"sync","from":from,"to":to,"updates":"all"}));
            }
        }
    }
    json!({"schema":1,"name":format!("random-seed-{seed}"),"seed":seed,"replicas":[101,202,303],"roots":{"text":"text","array":"array","map":"map"},"steps":steps})
}

#[derive(Debug)]
pub struct Failure {
    pub kind: &'static str,
    pub detail: String,
    pub exact_packets: Option<Json>,
}
impl std::fmt::Display for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.kind, self.detail)
    }
}
fn failure(kind: &'static str, detail: impl Into<String>) -> Failure {
    Failure {
        kind,
        detail: detail.into(),
        exact_packets: None,
    }
}
fn checked<T>(kind: &'static str, result: Result<T>) -> std::result::Result<T, Failure> {
    result.map_err(|error| failure(kind, error))
}

/// A saved check selects the same property and RNG, rather than falling back
/// to a semantic oracle comparison that could pass a convergence regression.
pub fn replay(trace: &Json) -> std::result::Result<(), Failure> {
    match trace["check"]["kind"].as_str().unwrap() {
        "update_properties" => update_properties(trace, trace["check"]["seed"].as_u64().unwrap() as u32),
        "packet_apply" => {
            let mut set = checked("invalid_trace", ReplicaSet::new(trace))?;
            for step in trace["steps"].as_array().unwrap() {
                checked("permutation_apply", set.step(step))?;
            }
            Ok(())
        }
        _ => Err(failure("invalid_check", "unknown property check")),
    }
}
pub fn regression(trace: &Json, error: &Failure, seed: u32) -> Json {
    let mut saved = error.exact_packets.clone().unwrap_or_else(|| trace.clone());
    saved["check"] = json!({"kind":if error.exact_packets.is_some(){"packet_apply"}else{"update_properties"},
        "seed":seed,"failure_kind":error.kind});
    if error.kind == "invalid_trace" {
        return saved;
    }
    minimize_by(
        &saved,
        |candidate| matches!(replay(candidate),Err(e) if e.kind == error.kind),
    )
}

pub fn update_properties(trace: &Json, seed: u32) -> std::result::Result<(), Failure> {
    let mut native = checked("invalid_trace", ReplicaSet::new(trace))?;
    for (i, step) in trace["steps"].as_array().unwrap().iter().enumerate() {
        checked("invalid_trace", native.step(step).map_err(|e| format!("step {i}: {e}")))?;
    }
    let packets: Vec<_> = native.messages.iter().flatten().collect();
    let mut random = Random::new(seed);
    let mut expected = None;
    for round in 0..5 {
        let mut order: Vec<_> = (0..packets.len()).collect();
        random.shuffle(&mut order);
        let extra = (0..packets.len() / 2)
            .map(|_| random.next(packets.len()))
            .collect::<Vec<_>>();
        order.extend(extra);
        random.shuffle(&mut order);
        let mut d = checked("invalid_trace", make(trace, 700001 + round))?;
        for (arrival, index) in order.iter().enumerate() {
            if let Err(e) = codec(d.apply_update_from_binary_v1(packets[*index])) {
                let mut input = trace.clone();
                input["name"] = json!(format!("permutation-seed-{seed}"));
                input["replicas"] =
                    json!([vec![json!(700001)], trace["replicas"].as_array().unwrap().clone()].concat());
                input["steps"] = json!(
                    order[..=arrival]
                        .iter()
                        .map(|index| json!({"op":"apply","at":0,"update":encode_hex(packets[*index])}))
                        .collect::<Vec<_>>()
                );
                return Err(Failure {
                    kind: "permutation_apply",
                    detail: format!("seed={seed} round={round} arrival={arrival} packet={index}: {e}"),
                    exact_packets: Some(input),
                });
            }
        }
        let state = checked("permutation_snapshot", snapshot(&d, trace))?;
        if state["pending"] != false {
            return Err(failure("pending", format!("seed={seed} round={round}")));
        }
        if let Some(expected) = &expected {
            if expected != &state {
                return Err(failure(
                    "permutation_mismatch",
                    format!("seed={seed} round={round} order={order:?}\n{state}\n{expected}"),
                ));
            }
        } else {
            expected = Some(state.clone());
        }
        for index in &order {
            checked(
                "idempotence_apply",
                codec(d.apply_update_from_binary_v1(packets[*index])),
            )?;
        }
        if checked("idempotence_snapshot", snapshot(&d, trace))? != state {
            return Err(failure("idempotence_mismatch", format!("seed={seed} round={round}")));
        }
        let encoded = checked("codec_encode", codec(d.encode_update_v1()))?;
        let canonical = checked(
            "codec_encode",
            codec(checked("codec_decode", codec(Update::decode_v1(&encoded)))?.encode_v1()),
        )?;
        let again = checked(
            "codec_encode",
            codec(checked("codec_decode", codec(Update::decode_v1(&canonical)))?.encode_v1()),
        )?;
        if canonical != again {
            return Err(failure("codec_fixed_point", format!("seed={seed} round={round}")));
        }
        let mut reopened = checked("invalid_trace", make(trace, 710001 + round))?;
        checked("reopen_apply", codec(reopened.apply_update_from_binary_v1(canonical)))?;
        if checked("reopen_snapshot", snapshot(&reopened, trace))? != state {
            return Err(failure("reopen_mismatch", format!("seed={seed} round={round}")));
        }
    }
    Ok(())
}
