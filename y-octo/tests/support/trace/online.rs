use std::{
    io::{BufRead, BufReader, Write},
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
};

use super::*;

#[derive(Debug)]
pub struct Failure {
    pub kind: &'static str,
    pub direction: &'static str,
    pub version: String,
    pub step: Option<usize>,
    pub detail: String,
}
impl std::fmt::Display for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {} {} step {:?}: {}",
            self.kind, self.direction, self.version, self.step, self.detail
        )
    }
}
impl Failure {
    fn shrinkable(&self) -> bool {
        !matches!(self.kind, "invalid_operation" | "protocol_failure")
    }
}
#[derive(Debug)]
enum RequestError {
    Protocol(String),
    Rejected { code: String, detail: String },
}
impl RequestError {
    fn context(self, version: &str, step: Option<usize>, direction: &'static str, operation: &str) -> Failure {
        let (kind, detail) = match self {
            Self::Protocol(error) => ("protocol_failure", error),
            Self::Rejected { code, detail } => (
                match code.as_str() {
                    "cross_apply_rejected" => "cross_apply_rejected",
                    "invalid_operation" => "invalid_operation",
                    _ => "protocol_failure",
                },
                detail,
            ),
        };
        Failure {
            kind,
            direction,
            version: version.into(),
            step,
            detail: format!("{operation}: {detail}"),
        }
    }
}

pub struct Oracle {
    child: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
}
impl Oracle {
    pub fn start() -> Result<Self> {
        let script = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/oracle/trace.mjs");
        let mut child = Command::new("node")
            .arg(script)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(|e| format!("start pinned Node oracle: {e}; run npm ci --prefix y-octo/tests/oracle"))?;
        let input = child.stdin.take().unwrap();
        let output = BufReader::new(child.stdout.take().unwrap());
        Ok(Self { child, input, output })
    }
    fn request(&mut self, request: Json) -> std::result::Result<Json, RequestError> {
        serde_json::to_writer(&mut self.input, &request).map_err(|e| RequestError::Protocol(e.to_string()))?;
        self.input
            .write_all(b"\n")
            .map_err(|e| RequestError::Protocol(e.to_string()))?;
        self.input.flush().map_err(|e| RequestError::Protocol(e.to_string()))?;
        let mut line = String::new();
        if self
            .output
            .read_line(&mut line)
            .map_err(|e| RequestError::Protocol(e.to_string()))?
            == 0
        {
            return Err(RequestError::Protocol("oracle subprocess ended before replying".into()));
        }
        let response: Json =
            serde_json::from_str(&line).map_err(|e| RequestError::Protocol(format!("oracle protocol: {e}: {line}")))?;
        match response["ok"].as_bool() {
            Some(true) => Ok(response["result"].clone()),
            Some(false) => Err(RequestError::Rejected {
                code: response["code"].as_str().unwrap_or("protocol_failure").into(),
                detail: response["error"].to_string(),
            }),
            None => Err(RequestError::Protocol(format!("invalid oracle response: {response}"))),
        }
    }
    pub fn replay_updates<'a>(
        &mut self,
        trace: &Json,
        version: &str,
        updates: impl IntoIterator<Item = &'a [u8]>,
    ) -> Result<Json> {
        self.request(json!({"kind":"reset","trace":trace,"version":version}))
            .map_err(|e| e.context(version, None, "setup", "reset").to_string())?;

        let mut snapshot = Json::Null;
        for (index, update) in updates.into_iter().enumerate() {
            let response = self
                .request(json!({"kind":"cross","at":0,"update":encode_hex(update)}))
                .map_err(|e| e.context(version, Some(index), "Rust->Yjs", "apply update").to_string())?;
            snapshot = response["snapshot"].clone();
        }
        Ok(snapshot)
    }

    /// Native lanes author independently; cross mirrors consume actual bytes.
    pub fn compare(&mut self, trace: &Json, version: &str) -> std::result::Result<(), Failure> {
        self.request(json!({"kind":"reset","trace":trace,"version":version}))
            .map_err(|e| e.context(version, None, "setup", "reset"))?;
        let setup = |e| Failure {
            kind: "invalid_operation",
            direction: "native",
            version: version.into(),
            step: None,
            detail: e,
        };
        let mut native = ReplicaSet::new(trace).map_err(setup)?;
        let mut mirrors = ReplicaSet::mirror(trace).map_err(setup)?;
        let mut rust_cross = ReplicaSet::mirror(trace).map_err(setup)?;
        for (i, step) in trace["steps"].as_array().unwrap().iter().enumerate() {
            let fail = |kind, direction, detail: String| Failure {
                kind,
                direction,
                version: version.into(),
                step: Some(i),
                detail: format!("{} {step}: {detail}", trace["name"]),
            };
            let js = self
                .request(json!({"kind":"step","step":step}))
                .map_err(|e| e.context(version, Some(i), "Yjs native", &step.to_string()))?;
            let at = native
                .step(step)
                .map_err(|e| fail("native_operation_rejected", "Rust native", e))?;
            for (replica, doc) in native.docs.iter().enumerate() {
                let got = semantic(&snapshot(doc, trace).map_err(|e| fail("snapshot_rejected", "Rust native", e))?);
                let expected = semantic(&js["snapshots"][replica]);
                if got != expected {
                    return Err(fail(
                        "native_semantic_mismatch",
                        "native",
                        format!("replica {replica}\nRust={got}\nYjs={expected}"),
                    ));
                }
            }
            codec(mirrors[at].apply_update_from_binary_v1(decode_hex(js["full"].as_str().unwrap())))
                .map_err(|e| fail("cross_apply_rejected", "Yjs->Rust", e))?;
            let got = snapshot(&mirrors[at], trace).map_err(|e| fail("snapshot_rejected", "Yjs->Rust", e))?;
            if got != js["snapshots"][at] {
                return Err(fail(
                    "cross_state_mismatch",
                    "Yjs->Rust",
                    format!("Rust={got}\nYjs={}", js["snapshots"][at]),
                ));
            }
            let full =
                codec(native.docs[at].encode_update_v1()).map_err(|e| fail("encode_rejected", "Rust native", e))?;
            let js_from_rust = self
                .request(json!({"kind":"cross","at":at,"update":encode_hex(&full)}))
                .map_err(|e| e.context(version, Some(i), "Rust->Yjs", &step.to_string()))?;
            let rust = snapshot(&native.docs[at], trace).map_err(|e| fail("snapshot_rejected", "Rust native", e))?;
            if semantic(&js_from_rust["snapshot"]) != semantic(&rust) {
                return Err(fail(
                    "cross_state_mismatch",
                    "Rust->Yjs",
                    format!("Rust={rust}\nYjs={}", js_from_rust["snapshot"]),
                ));
            }
            // Yjs can author formatting-cleanup deletes. Compare causal data
            // after both separate mirrors receive those derived bytes as well.
            codec(rust_cross[at].apply_update_from_binary_v1(full))
                .map_err(|e| fail("cross_apply_rejected", "Rust->Rust", e))?;
            codec(rust_cross[at].apply_update_from_binary_v1(decode_hex(js_from_rust["full"].as_str().unwrap())))
                .map_err(|e| fail("cross_apply_rejected", "Yjs->Rust", format!("cleanup: {e}")))?;
            let closed = snapshot(&rust_cross[at], trace).map_err(|e| fail("snapshot_rejected", "Rust->Yjs", e))?;
            if closed != js_from_rust["snapshot"] {
                return Err(fail(
                    "cross_causal_mismatch",
                    "Rust->Yjs",
                    format!("Rust={closed}\nYjs={}", js_from_rust["snapshot"]),
                ));
            }
        }
        Ok(())
    }
}
impl Drop for Oracle {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Shrink only a valid candidate with the original failure class and direction.
pub fn minimize(oracle: &mut Oracle, trace: &Json, version: &str, error: &Failure) -> Json {
    let mut saved = trace.clone();
    saved["check"] =
        json!({"kind":"differential","version":version,"failure_kind":error.kind,"direction":error.direction});
    if !error.shrinkable() {
        return saved;
    }
    super::minimize_by(
        &saved,
        |candidate| matches!(oracle.compare(candidate,version),Err(e) if e.kind==error.kind&&e.direction==error.direction),
    )
}
