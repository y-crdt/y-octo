use serde_json::Value as Json;
use sha2::{Digest, Sha256};

/// Explicit tagged encoding shared with oracle/digest.mjs. Object keys use
/// UTF-8 byte order, and numbers use IEEE-754 rather than JSON formatter
/// output.
pub fn digest(value: &Json) -> String {
    fn length(hash: &mut Sha256, n: usize) {
        hash.update(u32::try_from(n).unwrap().to_be_bytes());
    }
    fn visit(hash: &mut Sha256, value: &Json) {
        match value {
            Json::Null => hash.update([0]),
            Json::Bool(false) => hash.update([1]),
            Json::Bool(true) => hash.update([2]),
            Json::Number(n) => {
                hash.update([3]);
                hash.update(n.as_f64().unwrap().to_be_bytes());
            }
            Json::String(s) => {
                hash.update([4]);
                length(hash, s.len());
                hash.update(s.as_bytes());
            }
            Json::Array(v) => {
                hash.update([5]);
                length(hash, v.len());
                for v in v {
                    visit(hash, v);
                }
            }
            Json::Object(v) => {
                hash.update([6]);
                length(hash, v.len());
                let mut keys = v.keys().collect::<Vec<_>>();
                keys.sort_unstable();
                for k in keys {
                    let v = &v[k];
                    visit(hash, &Json::String(k.clone()));
                    visit(hash, v);
                }
            }
        }
    }
    let mut hash = Sha256::new();
    visit(&mut hash, value);
    hash.finalize().iter().map(|b| format!("{b:02x}")).collect()
}
