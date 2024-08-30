use super::*;
use napi::bindgen_prelude::Buffer;
use y_octo::{
    read_doc_message, write_doc_message, CrdtRead, CrdtWrite, Doc, DocMessage, RawDecoder, RawEncoder, StateVector,
};

#[napi(js_name = "Protocol")]
pub struct YProtocol {
    pub(crate) doc: Doc,
}

#[napi]
impl YProtocol {
    #[napi(constructor)]
    pub fn new(doc: &YDoc) -> Self {
        Self { doc: doc.doc.clone() }
    }

    #[napi]
    pub fn encode_sync_step(&self, step: u8, buffer: Option<Buffer>) -> Result<Buffer> {
        match step {
            1 => {
                let sv = self.doc.get_state_vector();
                let mut encoder = RawEncoder::default();
                sv.write(&mut encoder)?;

                let mut buffer = vec![];
                write_doc_message(&mut buffer, &DocMessage::Step1(encoder.into_inner()))?;
                Ok(buffer.into())
            }
            2 => {
                if let Some(sv) = buffer {
                    let sv = StateVector::read(&mut RawDecoder::new(&sv))?;
                    let update = self.doc.encode_state_as_update_v1(&sv)?;
                    let mut buffer = vec![];
                    write_doc_message(&mut buffer, &DocMessage::Step2(update)).unwrap();
                    Ok(buffer.into())
                } else {
                    Err(anyhow::Error::msg("State vector is required for sync step 2.").into())
                }
            }
            3 => {
                let update = if let Some(update) = buffer {
                    update.to_vec()
                } else {
                    self.doc.encode_update_v1()?
                };
                let mut buffer = vec![];
                write_doc_message(&mut buffer, &DocMessage::Update(update)).unwrap();
                Ok(buffer.into())
            }
            _ => Err(anyhow::Error::msg("Invalid sync step. Must be 1, 2, or 3.").into()),
        }
    }

    #[napi]
    pub fn apply_sync_step(&mut self, buffer: Buffer) -> Result<Option<Buffer>> {
        match read_doc_message(buffer.as_ref()) {
            Ok((tail, message)) => {
                if !tail.is_empty() {
                    return Err(anyhow::Error::msg("Invalid sync message buffer.").into());
                }
                Ok(match message {
                    DocMessage::Step1(sv) => Some(self.encode_sync_step(2, Some(sv.into()))?),
                    DocMessage::Step2(binary) | DocMessage::Update(binary) => {
                        self.doc.apply_update_from_binary_v1(binary)?;
                        None
                    }
                })
            }
            Err(e) => Err(anyhow::Error::msg(format!("Invalid sync message buffer: {}", e.to_string())).into()),
        }
    }
}
