pub mod generate;
pub mod online;
pub mod trajectory;
// Test-only operation trace interpreter. No oracle process is started here.
use std::collections::BTreeMap;

use serde_json::{Value as Json, json};
use y_octo::{Any, Doc, DocOptions, StateVector, TextDeltaOp, TextInsert, TypeIdentity, Update, Value};

type Result<T> = std::result::Result<T, String>;
fn codec<T>(value: y_octo::JwstCodecResult<T>) -> Result<T> {
    value.map_err(|e| e.to_string())
}

pub fn decode_hex(hex: &str) -> Vec<u8> {
    super::bytes(&json!(hex))
}
pub fn encode_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
fn number(n: f64) -> Json {
    if n == 0.0 && n.is_sign_negative() {
        json!({"$any":"-0"})
    } else if !n.is_finite() {
        json!({"$any":if n.is_nan(){"NaN"}else if n.is_sign_negative(){"-Infinity"}else{"Infinity"}})
    } else if n.fract() == 0.0 && n.abs() < 9_007_199_254_740_992.0 {
        json!(n as i64)
    } else {
        json!(n)
    }
}
fn any_json(v: &Any) -> Json {
    match v {
        Any::Undefined => json!({"$any":"undefined"}),
        Any::Null => Json::Null,
        Any::True => json!(true),
        Any::False => json!(false),
        Any::Integer(v) => json!(v),
        Any::Float32(v) => number(v.0 as f64),
        Any::Float64(v) => number(v.0),
        Any::BigInt64(v) => json!({"$any":"bigint","value":v.to_string()}),
        Any::String(v) => json!(v),
        Any::Binary(v) => json!({"$any":"binary","hex":encode_hex(v)}),
        Any::Array(v) => Json::Array(v.iter().map(any_json).collect()),
        Any::Object(v) => Json::Object(v.iter().map(|(k, v)| (k.clone(), any_json(v))).collect()),
    }
}
fn any(v: &Json) -> Any {
    if let Some(tag) = v.get("$any").and_then(Json::as_str) {
        return match tag {
            "undefined" => Any::Undefined,
            "-0" => Any::Float64((-0.0_f64).into()),
            "NaN" => Any::from(f64::NAN),
            "Infinity" => Any::from(f64::INFINITY),
            "-Infinity" => Any::from(f64::NEG_INFINITY),
            "bigint" => Any::BigInt64(v["value"].as_str().unwrap().parse().unwrap()),
            "binary" => Any::Binary(decode_hex(v["hex"].as_str().unwrap())),
            _ => panic!("unknown trace Any {tag}"),
        };
    }
    match v {
        Json::Null => Any::Null,
        Json::Bool(v) => Any::from(*v),
        Json::String(v) => Any::String(v.clone()),
        Json::Number(v) => v
            .as_i64()
            .map(Any::from)
            .unwrap_or_else(|| Any::from(v.as_f64().unwrap())),
        Json::Array(v) => Any::Array(v.iter().map(any).collect()),
        Json::Object(v) => Any::Object(Box::new(v.iter().map(|(k, v)| (k.clone(), any(v))).collect())),
    }
}
// Any::Array is the public insertion API's batch spelling. A trace operation
// inserts one JSON value, so an array literal is one element in that batch.
fn single_value(value: &Json) -> Value {
    match any(value) {
        value @ Any::Array(_) => Value::from_vec(vec![value]),
        value => Value::Any(value),
    }
}
fn attributes(v: &Json) -> BTreeMap<String, Any> {
    v.as_object()
        .map(|v| v.iter().map(|(k, v)| (k.clone(), any(v))).collect())
        .unwrap_or_default()
}
fn delta(t: &y_octo::Text) -> Json {
    let mut out = Vec::new();
    for op in t.to_delta() {
        if let TextDeltaOp::Insert { insert, format } = op {
            let attrs: serde_json::Map<_, _> = format
                .unwrap_or_default()
                .iter()
                .map(|(k, v)| (k.clone(), any_json(v)))
                .collect();
            let values = match insert {
                TextInsert::Text(v) => vec![json!(v)],
                TextInsert::Embed(v) => v.iter().map(any_json).collect(),
            };
            for insert in values {
                let mut op = json!({"insert":insert});
                if !attrs.is_empty() {
                    op["attributes"] = Json::Object(attrs.clone());
                }
                out.push(op);
            }
        }
    }
    normalize_delta(json!(out))
}
pub fn normalize_delta(delta: Json) -> Json {
    let mut out: Vec<Json> = Vec::new();
    for op in delta.as_array().unwrap() {
        if let Some(last) = out.last_mut()
            && last["attributes"] == op["attributes"]
            && let (Some(a), Some(b)) = (last["insert"].as_str(), op["insert"].as_str())
        {
            last["insert"] = json!(format!("{a}{b}"));
            continue;
        }
        out.push(op.clone());
    }
    json!(out)
}
fn identity(id: Option<y_octo::Id>) -> Json {
    id.map(|id| json!([id.client, id.clock])).unwrap_or(Json::Null)
}
fn shape(value: Value, path: &str, missing: &mut Option<Vec<(String, String)>>) -> Result<Json> {
    Ok(match value {
        Value::Any(v) => json!({"kind":"any","value":any_json(&v)}),
        Value::Text(t) => {
            let id = match codec(t.identity())? {
                TypeIdentity::Item(id) => identity(Some(id)),
                TypeIdentity::Root(_) => Json::Null,
            };
            let runs = match codec(t.identity_runs()) {
                Ok(runs) => Some(runs),
                Err(error) => {
                    if let Some(errors) = missing {
                        errors.push((path.to_string(), error));
                        None
                    } else {
                        return Err(error);
                    }
                }
            };
            let units = runs.map(|runs| {
                runs.into_iter()
                    .flat_map(|run| {
                        let chars = match run.insert {
                            TextInsert::Text(s) => s.encode_utf16().collect::<Vec<_>>(),
                            TextInsert::Embed(_) => Vec::new(),
                        };
                        chars
                            .into_iter()
                            .enumerate()
                            .map(move |(offset, ch)| json!([run.id.client, run.id.clock + offset as u64, ch]))
                    })
                    .collect::<Vec<_>>()
            });
            let mut result = json!({"kind":"text","id":id,"text":t.to_string(),"delta":delta(&t)});
            if let Some(units) = units {
                result["units"] = json!(units);
            }
            result
        }
        Value::Array(a) => {
            let values: Vec<_> = a.iter().collect();
            let values: std::result::Result<Vec<_>, _> = values
                .into_iter()
                .enumerate()
                .map(|(i, v)| shape(v, &format!("{path}/value/{i}"), missing))
                .collect();
            json!({"kind":"array","id":identity(a.id()),"value":values?})
        }
        Value::Map(m) => {
            let entries: Vec<_> = m.iter().map(|(k, v)| (k.to_owned(), v)).collect();
            let entries: Result<serde_json::Map<_, _>> = entries
                .into_iter()
                .map(|(k, v)| {
                    let child = shape(
                        v,
                        &format!("{path}/value/{}", k.replace('~', "~0").replace('/', "~1")),
                        missing,
                    )?;
                    Ok((k, child))
                })
                .collect();
            json!({"kind":"map","id":identity(m.id()),"value":entries?})
        }
        other => return Err(format!("trace cannot project {other:?}")),
    })
}
fn root(d: &Doc, kind: &str, name: &str) -> Result<Value> {
    match kind {
        "text" => Ok(Value::Text(codec(d.get_or_create_text(name))?)),
        "array" => Ok(Value::Array(codec(d.get_or_create_array(name))?)),
        "map" => Ok(Value::Map(codec(d.get_or_create_map(name))?)),
        _ => Err(format!("unsupported root kind {kind}")),
    }
}
fn make(trace: &Json, client: u64) -> Result<Doc> {
    let d = DocOptions {
        client_id: client,
        guid: format!("trace-{client}"),
        gc: trace["gc"].as_bool().unwrap_or(true),
    }
    .build();
    for (name, kind) in trace["roots"].as_object().unwrap() {
        root(&d, kind.as_str().unwrap(), name)?;
    }
    if let Some(roots) = trace["wire_roots"].as_object() {
        for (name, kind) in roots {
            root(&d, kind.as_str().unwrap(), name)?;
        }
    }
    Ok(d)
}
pub fn snapshot(d: &Doc, trace: &Json) -> Result<Json> {
    snapshot_inner(d, trace, &mut None)
}
/// Read every available field even when a text identity API rejects an embedded
/// shared type. Callers must separately match and account for every missing
/// path.
pub fn snapshot_available(d: &Doc, trace: &Json) -> Result<(Json, Vec<(String, String)>)> {
    let mut missing = Some(Vec::new());
    let state = snapshot_inner(d, trace, &mut missing)?;
    Ok((state, missing.unwrap()))
}
fn snapshot_inner(d: &Doc, trace: &Json, missing: &mut Option<Vec<(String, String)>>) -> Result<Json> {
    let mut roots = serde_json::Map::new();
    for (name, kind) in trace["roots"].as_object().unwrap() {
        roots.insert(
            name.clone(),
            shape(
                root(d, kind.as_str().unwrap(), name)?,
                &format!("/roots/{}", name.replace('~', "~0").replace('/', "~1")),
                missing,
            )?,
        );
    }
    let mut sv: Vec<_> = d.get_state_vector().iter().map(|(c, k)| (*c, *k)).collect();
    sv.sort_unstable();
    let mut ceiling = StateVector::default();
    for c in trace["replicas"].as_array().unwrap() {
        ceiling.set_max(c.as_u64().unwrap(), u64::MAX);
    }
    let mut update = codec(Update::decode_v1(codec(d.encode_state_as_update_v1(&ceiling))?))?;
    let mut ds = BTreeMap::<u64, Vec<(u64, u64)>>::new();
    for (client, r) in update.delete_set_iter(ceiling) {
        ds.entry(client).or_default().push((r.start, r.end - r.start));
    }
    let ds: Vec<_> = ds
        .into_iter()
        .map(|(c, mut ranges)| {
            ranges.sort_unstable();
            (c, ranges)
        })
        .collect();
    Ok(json!({"roots":roots,"sv":sv,"ds":ds,"pending":d.has_pending_updates()}))
}
pub fn semantic(snapshot: &Json) -> Json {
    fn strip(node: &mut Json) {
        let kind = node["kind"].as_str().unwrap().to_owned();
        node.as_object_mut().unwrap().remove("id");
        node.as_object_mut().unwrap().remove("units");
        match kind.as_str() {
            "map" => {
                for child in node["value"].as_object_mut().unwrap().values_mut() {
                    strip(child)
                }
            }
            "array" => {
                for child in node["value"].as_array_mut().unwrap() {
                    strip(child)
                }
            }
            _ => {}
        }
    }
    let mut roots = snapshot["roots"].clone();
    for root in roots.as_object_mut().unwrap().values_mut() {
        strip(root);
    }
    roots
}

pub struct ReplicaSet {
    pub trace: Json,
    pub docs: Vec<Doc>,
    pub messages: Vec<Vec<Vec<u8>>>,
}
impl ReplicaSet {
    pub fn new(trace: &Json) -> Result<Self> {
        let docs: Result<Vec<_>> = trace["replicas"]
            .as_array()
            .unwrap()
            .iter()
            .map(|c| make(trace, c.as_u64().unwrap()))
            .collect();
        let docs = docs?;
        let messages = docs.iter().map(|_| Vec::new()).collect();
        Ok(Self {
            trace: trace.clone(),
            docs,
            messages,
        })
    }
    pub fn mirror(trace: &Json) -> Result<Vec<Doc>> {
        trace["replicas"]
            .as_array()
            .unwrap()
            .iter()
            .enumerate()
            .map(|(i, _)| make(trace, 800000 + i as u64))
            .collect()
    }
    fn target(&self, at: usize, path: &Json) -> Result<Value> {
        let path = path.as_array().unwrap();
        let name = path[0].as_str().unwrap();
        let mut value = root(&self.docs[at], self.trace["roots"][name].as_str().unwrap(), name)?;
        for part in &path[1..] {
            value = match value {
                Value::Map(m) => m.get(part.as_str().unwrap()),
                Value::Array(a) => a.get(part.as_u64().unwrap()),
                _ => None,
            }
            .ok_or_else(|| format!("missing target {path:?}"))?;
        }
        Ok(value)
    }
    pub fn step(&mut self, step: &Json) -> Result<usize> {
        let op = step["op"].as_str().unwrap();
        let at = step[if op == "sync" { "to" } else { "at" }].as_u64().unwrap() as usize;
        let before = self.docs[at].get_state_vector();
        if op == "sync" {
            let from = step["from"].as_u64().unwrap() as usize;
            if let Some(since) = step["since"].as_array() {
                let mut state = StateVector::default();
                for entry in since {
                    state.set_max(entry[0].as_u64().unwrap(), entry[1].as_u64().unwrap());
                }
                let update = codec(self.docs[from].encode_state_as_update_v1(&state))?;
                codec(self.docs[at].apply_update_from_binary_v1(update))?;
            } else {
                let mut slots = if step["updates"] == "all" {
                    (0..self.messages[from].len()).collect::<Vec<_>>()
                } else {
                    step["updates"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|i| i.as_u64().unwrap() as usize)
                        .collect()
                };
                if step["reverse"] == true {
                    slots.reverse();
                }
                for _ in 0..step["repeat"].as_u64().unwrap_or(1) {
                    for i in &slots {
                        let update = self.messages[from]
                            .get(*i)
                            .ok_or_else(|| format!("unknown packet {from}/{i}"))?
                            .clone();
                        codec(self.docs[at].apply_update_from_binary_v1(update))?;
                    }
                }
            }
        } else if op == "apply" {
            codec(self.docs[at].apply_update_from_binary_v1(decode_hex(step["update"].as_str().unwrap())))?;
        } else if op == "gc" {
            codec(self.docs[at].gc())?;
        } else {
            let value = self.target(at, &step["target"])?;
            let position = position(&value, &step["index"], op.ends_with("remove"));
            let len = match &value {
                Value::Text(t) => t.len(),
                Value::Array(a) => a.len(),
                _ => 0,
            };
            let count = step["length"].as_u64().unwrap_or(1).min(len.saturating_sub(position));
            match (op, value) {
                ("text_insert", Value::Text(mut t)) => codec(t.insert(position, step["value"].as_str().unwrap()))?,
                ("text_remove", Value::Text(mut t)) => {
                    if len > 0 {
                        codec(t.remove(position, count))?;
                    }
                }
                ("format", Value::Text(mut t)) => {
                    if len > 0 {
                        codec(t.apply_delta(&[
                            TextDeltaOp::Retain {
                                retain: position,
                                format: None,
                            },
                            TextDeltaOp::Retain {
                                retain: count,
                                format: Some(attributes(&step["attributes"])),
                            },
                        ]))?;
                    }
                }
                ("text_embed", Value::Text(mut t)) => codec(t.apply_delta(&[
                    TextDeltaOp::Retain {
                        retain: position,
                        format: None,
                    },
                    TextDeltaOp::Insert {
                        insert: TextInsert::Embed(vec![any(&step["value"])]),
                        format: None,
                    },
                ]))?,
                ("array_insert", Value::Array(mut a)) => codec(a.insert(position, single_value(&step["value"])))?,
                ("array_remove", Value::Array(mut a)) => {
                    if len > 0 {
                        codec(a.remove(position, count))?;
                    }
                }
                ("map_insert", Value::Map(mut m)) => {
                    codec(m.insert(step["key"].as_str().unwrap().into(), single_value(&step["value"])))?
                }
                ("map_remove", Value::Map(mut m)) => m.remove(step["key"].as_str().unwrap()),
                ("create", parent) => {
                    let child = match step["kind"].as_str().unwrap() {
                        "text" => Value::Text(codec(self.docs[at].create_text())?),
                        "array" => Value::Array(codec(self.docs[at].create_array())?),
                        "map" => Value::Map(codec(self.docs[at].create_map())?),
                        kind => return Err(format!("unsupported shared type {kind}")),
                    };
                    match parent {
                        Value::Map(mut m) => codec(m.insert(step["key"].as_str().unwrap().into(), child))?,
                        Value::Array(mut a) => codec(a.insert(position, child))?,
                        _ => return Err("shared type parent must be map/array".into()),
                    }
                }
                _ => return Err(format!("invalid target for {op}")),
            }
        }
        let update = codec(self.docs[at].encode_state_as_update_v1(&before))?;
        self.messages[at].push(update);
        Ok(at)
    }
}
fn position(value: &Value, p: &Json, remove: bool) -> u64 {
    if let Some(index) = p.as_u64() {
        return index;
    }
    let mut positions = match value {
        Value::Text(t) => {
            let mut positions = vec![0];
            let mut n = 0;
            for op in t.to_delta() {
                if let TextDeltaOp::Insert { insert, .. } = op {
                    match insert {
                        TextInsert::Text(text) => {
                            for c in text.chars() {
                                n += c.len_utf16() as u64;
                                positions.push(n);
                            }
                        }
                        TextInsert::Embed(values) => {
                            for _ in values {
                                n += 1;
                                positions.push(n);
                            }
                        }
                    }
                }
            }
            positions
        }
        Value::Array(a) => (0..=a.len()).collect(),
        _ => vec![0],
    };
    if remove && positions.len() > 1 {
        positions.pop();
    }
    match p.as_str().unwrap_or("end") {
        "begin" => positions[0],
        "middle" => positions[(positions.len() - 1) / 2],
        "end" => *positions.last().unwrap(),
        _ => p.as_u64().unwrap(),
    }
}

/// Remove chunks while preserving a caller-verified failure. Invalid candidates
/// are rejected by the predicate, not reinterpreted as shorter counterexamples.
pub fn minimize_by(trace: &Json, mut fails: impl FnMut(&Json) -> bool) -> Json {
    let mut minimal = trace.clone();
    minimal.as_object_mut().unwrap().remove("expected");
    let mut chunk = (minimal["steps"].as_array().unwrap().len() / 2).max(1);
    while chunk > 0 {
        let mut start = 0;
        while start < minimal["steps"].as_array().unwrap().len() {
            let mut candidate = minimal.clone();
            let steps = candidate["steps"].as_array_mut().unwrap();
            let end = (start + chunk).min(steps.len());
            steps.drain(start..end);
            if fails(&candidate) {
                minimal = candidate;
                start = 0;
            } else {
                start += chunk;
            }
        }
        chunk /= 2;
    }
    minimal
}

pub fn save_failure(trace: &Json, label: &str) -> String {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("target/trace-failures");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{label}.json"));
    let json = serde_json::to_string_pretty(trace).unwrap();
    std::fs::write(&path, &json).unwrap();
    format!("minimized trace saved to {}:\n{json}", path.display())
}
