use napi::{bindgen_prelude::Object as JsObject, Env};
use y_octo::{prefer_small_random, Awareness};

use super::*;

#[napi(js_name = "Awareness")]
pub struct YAwareness {
    pub(crate) awareness: Awareness,
}

#[napi]
impl YAwareness {
    #[napi(constructor)]
    pub fn new(client_id: Option<i64>) -> Self {
        let client_id = client_id
            .and_then(|c| c.try_into().ok())
            .unwrap_or_else(|| prefer_small_random());
        Self {
            awareness: Awareness::new(client_id as u64),
        }
    }

    #[napi(getter)]
    pub fn client_id(&self) -> i64 {
        self.awareness.local_id() as i64
    }

    #[napi(
        getter,
        ts_generic_types = "T = Record<string, any>",
        ts_return_type = "Record<string, T>"
    )]
    pub fn states(&self, env: Env) -> Result<JsObject> {
        let mut object = env.create_object()?;
        for (k, v) in self.awareness.get_states() {
            let value = env.to_js_value(&serde_json::from_str(&v.content())?)?;
            object.set_named_property(&k.to_string(), value)?;
        }
        Ok(object)
    }
}
