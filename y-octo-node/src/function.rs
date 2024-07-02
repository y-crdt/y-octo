use napi::bindgen_prelude::Buffer as JsBuffer;
use y_octo::merge_updates_v1;

use super::*;

#[napi]
pub fn encode_state_as_update(doc: &YDoc, state: Option<JsBuffer>) -> Result<JsBuffer> {
    doc.encode_state_as_update_v1(state)
}

#[napi]
pub fn apply_update(doc: &mut YDoc, update: JsBuffer) -> Result<()> {
    doc.apply_update(update)
}

#[napi]
pub fn merge_updates(updates: Vec<JsBuffer>) -> Result<JsBuffer> {
    let updates = updates.iter().map(|u| u.as_ref()).collect::<Vec<_>>();
    Ok(merge_updates_v1(updates)?.encode_v1()?.into())
}
