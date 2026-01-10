use y_octo::{CrdtWrite, DeleteSet, Doc, Id, RawEncoder, StateVector};

use super::*;

#[napi(js_name = "Id")]
pub struct YId {
    pub(crate) id: Id,
}

#[napi(js_name = "Store")]
pub struct YStore {
    pub(crate) doc: Doc,
}

#[napi(js_name = "DeleteSet")]
#[derive(PartialEq)]
pub struct YDeleteSet {
    pub(crate) ds: DeleteSet,
}

#[napi]
pub struct YSnapshot {
    ds: DeleteSet,
    sv: StateVector,
}

impl YSnapshot {
    pub fn from_doc(doc: &YDoc) -> Self {
        Self {
            ds: doc.doc.get_delete_sets(),
            sv: doc.doc.get_state_vector(),
        }
    }

    pub fn encode_v1(&self) -> Result<Vec<u8>> {
        let mut encoder = RawEncoder::default();
        self.ds.write(&mut encoder)?;
        self.sv.write(&mut encoder)?;
        Ok(encoder.into_inner())
    }
}
