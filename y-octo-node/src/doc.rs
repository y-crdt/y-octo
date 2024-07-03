use napi::{
    bindgen_prelude::{Buffer as JsBuffer, JsFunction},
    threadsafe_function::{ErrorStrategy, ThreadsafeFunction, ThreadsafeFunctionCallMode},
};
use y_octo::{CrdtRead, Doc, History, RawDecoder, StateVector};

use super::*;

#[napi(js_name = "Doc")]
pub struct YDoc {
    pub(crate) doc: Doc,
}

#[napi]
impl YDoc {
    #[napi(constructor)]
    pub fn new(client_id: Option<i64>) -> Self {
        Self {
            doc: if let Some(client_id) = client_id {
                Doc::with_client(client_id as u64)
            } else {
                Doc::default()
            },
        }
    }

    #[napi(getter)]
    pub fn client_id(&self) -> i64 {
        self.doc.client() as i64
    }

    #[napi(getter)]
    pub fn guid(&self) -> &str {
        self.doc.guid()
    }

    #[napi(getter)]
    pub fn store(&self) -> YStore {
        YStore { doc: self.doc.clone() }
    }

    #[napi(getter)]
    pub fn keys(&self) -> Vec<String> {
        self.doc.keys()
    }

    #[napi]
    pub fn get_or_create_array(&self, key: String) -> Result<YArray> {
        self.doc
            .get_or_create_array(key)
            .map(YArray::inner_new)
            .map_err(anyhow::Error::from)
    }

    #[napi]
    pub fn get_or_create_text(&self, key: String) -> Result<YText> {
        self.doc
            .get_or_create_text(key)
            .map(YText::inner_new)
            .map_err(anyhow::Error::from)
    }

    #[napi]
    pub fn get_or_create_map(&self, key: String) -> Result<YMap> {
        self.doc
            .get_or_create_map(key)
            .map(YMap::inner_new)
            .map_err(anyhow::Error::from)
    }

    #[napi]
    pub fn create_array(&self) -> Result<YArray> {
        self.doc
            .create_array()
            .map(YArray::inner_new)
            .map_err(anyhow::Error::from)
    }

    #[napi]
    pub fn create_text(&self) -> Result<YText> {
        self.doc
            .create_text()
            .map(YText::inner_new)
            .map_err(anyhow::Error::from)
    }

    #[napi]
    pub fn create_map(&self) -> Result<YMap> {
        self.doc.create_map().map(YMap::inner_new).map_err(anyhow::Error::from)
    }

    #[napi]
    pub fn apply_update(&mut self, update: JsBuffer) -> Result<()> {
        self.doc.apply_update_from_binary_v1(update)?;

        Ok(())
    }

    #[napi]
    pub fn encode_state_as_update_v1(&self, state: Option<JsBuffer>) -> Result<JsBuffer> {
        let result = match state {
            Some(state) => {
                let mut decoder = RawDecoder::new(state.as_ref());
                let state = StateVector::read(&mut decoder)?;
                self.doc.encode_state_as_update_v1(&state)
            }
            None => self.doc.encode_update_v1(),
        };

        result.map(|v| v.into()).map_err(anyhow::Error::from)
    }

    #[napi]
    pub fn gc(&self) -> Result<()> {
        self.doc.gc().map_err(anyhow::Error::from)
    }

    #[napi(ts_args_type = "callback: (result: Uint8Array) => void")]
    pub fn on_update(&mut self, callback: JsFunction) -> Result<()> {
        let tsfn: ThreadsafeFunction<JsBuffer, ErrorStrategy::Fatal> =
            callback.create_threadsafe_function(0, |ctx| Ok(vec![ctx.value]))?;

        let callback = move |update: &[u8], _h: &[History]| {
            tsfn.call(JsBuffer::from(update.to_vec()), ThreadsafeFunctionCallMode::Blocking);
        };
        self.doc.subscribe(Box::new(callback));
        Ok(())
    }

    #[napi]
    pub fn transact(&mut self, callback: JsFunction) -> Result<()> {
        callback.call_without_args(None)?;
        self.doc.gc()?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_doc_client() {
        let client_id = 1;
        let doc = YDoc::new(Some(client_id));
        assert_eq!(doc.client_id(), 1);
    }

    #[test]
    fn test_doc_guid() {
        let doc = YDoc::new(None);
        assert_eq!(doc.guid().len(), 21);
    }

    #[test]
    fn test_create_array() {
        let doc = YDoc::new(None);
        let array = doc.get_or_create_array("array".into()).unwrap();
        assert_eq!(array.length(), 0);
    }

    #[test]
    fn test_create_text() {
        let doc = YDoc::new(None);
        let text = doc.get_or_create_text("text".into()).unwrap();
        assert_eq!(text.len(), 0);
    }

    #[test]
    fn test_keys() {
        let doc = YDoc::new(None);
        doc.get_or_create_array("array".into()).unwrap();
        doc.get_or_create_text("text".into()).unwrap();
        doc.get_or_create_map("map".into()).unwrap();
        let mut keys = doc.keys();
        keys.sort();
        assert_eq!(keys, vec!["array", "map", "text"]);
    }
}
