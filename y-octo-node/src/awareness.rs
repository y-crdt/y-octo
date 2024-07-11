use napi::{
    bindgen_prelude::{Array as JsArray, Buffer as JsBuffer, JsFunction},
    threadsafe_function::{ErrorStrategy, ThreadsafeFunction, ThreadsafeFunctionCallMode},
    Env, JsString, JsUnknown,
};
use y_octo::{prefer_small_random, Awareness, CrdtRead, Doc, History, RawDecoder, StateVector};

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
}
