use napi::{bindgen_prelude::Buffer as JsBuffer, Env, JsUnknown};
use y_octo::{merge_updates_v1, CrdtWrite, RawEncoder};

use super::*;

// state

#[napi]
pub fn encode_state_as_update(doc: &YDoc, state: Option<JsBuffer>) -> Result<JsBuffer> {
    doc.encode_state_as_update_v1(state)
}

#[napi]
pub fn encode_state_vector(doc: &YDoc) -> Result<JsBuffer> {
    let sv = doc.doc.get_state_vector();
    let mut encoder = RawEncoder::default();
    sv.write(&mut encoder)?;
    Ok(encoder.into_inner().into())
}

// delete set

#[napi]
pub fn create_delete_set_from_struct_store(store: &YStore) -> YDeleteSet {
    YDeleteSet {
        ds: store.doc.get_delete_sets(),
    }
}

#[napi]
pub fn equal_delete_sets(a: &YDeleteSet, b: &YDeleteSet) -> bool {
    a == b
}

// snapshot

#[napi]
pub fn snapshot(doc: &YDoc) -> YSnapshot {
    YSnapshot::from_doc(doc)
}

#[napi]
pub fn encode_snapshot(snapshot: &YSnapshot) -> Result<JsBuffer> {
    Ok(snapshot.encode_v1()?.into())
}

// update

#[napi]
pub fn apply_update(doc: &mut YDoc, update: JsBuffer) -> Result<()> {
    doc.apply_update(update)
}

#[napi]
pub fn merge_updates(updates: Vec<JsBuffer>) -> Result<JsBuffer> {
    let updates = updates.iter().map(|u| u.as_ref()).collect::<Vec<_>>();
    Ok(merge_updates_v1(updates)?.encode_v1()?.into())
}

#[napi]
pub fn is_abstract_type(env: Env, unknown: JsUnknown) -> Result<bool> {
    Ok(YArray::instance_of(env, &unknown)? || YMap::instance_of(env, &unknown)? || YText::instance_of(env, &unknown)?)
}
