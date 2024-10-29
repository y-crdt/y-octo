use napi::{
    bindgen_prelude::{Array as JsArray, Buffer as JsBuffer, JsFunction},
    threadsafe_function::{ErrorStrategy, ThreadsafeFunction, ThreadsafeFunctionCallMode},
    Env, JsString, JsUnknown,
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

    #[napi(setter)]
    pub fn set_client_id(&mut self, client_id: i64) {
        self.doc.set_client(client_id as u64);
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
    pub fn create_text(&self, text: Option<String>) -> Result<YText> {
        let mut ytext = self.doc.create_text().map(YText::inner_new)?;
        if let Some(text) = text {
            ytext.insert(0, text)?;
        }
        Ok(ytext)
    }

    #[napi(ts_args_type = "entries?: Array<[string,any]> | Iterator<[string,any]>")]
    pub fn create_map(&self, env: Env, entries: Option<JsArray>) -> Result<YMap> {
        let mut ymap = self.doc.create_map().map(YMap::inner_new)?;
        if let Some(entries) = entries {
            for i in 0..entries.len() {
                if let Ok(Some(value)) = entries.get::<JsArray>(i) {
                    let key = value.get::<JsString>(0)?;
                    let value = value.get::<JsUnknown>(1)?;
                    if let (Some(key), Some(value)) = (key, value) {
                        ymap.set(env, key.into_utf8()?.into_owned()?, MixedRefYType::D(value))?;
                        continue;
                    }
                }

                return Err(anyhow::anyhow!("Invalid entry"));
            }
        }

        Ok(ymap)
    }

    #[napi]
    pub fn apply_update(&mut self, update: JsBuffer) -> Result<()> {
        let client = self.doc.client();
        let before_current_state = self.doc.get_state_vector().get(&client);

        self.doc.apply_update_from_binary_v1(update)?;

        // if update received from remote and  current client state has been changed
        // that means another client using same client id, we need to change the client
        // id to avoid conflict
        if self.doc.get_state_vector().get(&client) != before_current_state {
            self.doc.renew_client();
        }

        Ok(())
    }

    #[napi]
    pub fn diff(&self, sv: Option<JsBuffer>) -> Result<Option<JsBuffer>> {
        if let Some(sv) = sv {
            let mut decoder = RawDecoder::new(sv.as_ref());
            let state = StateVector::read(&mut decoder)?;
            let update = self.doc.encode_state_as_update_v1(&state)?;
            Ok(Some(update.into()))
        } else {
            Ok(None)
        }
    }

    #[napi]
    pub fn encode_state_as_update_v1(&self, state: Option<JsBuffer>) -> Result<JsBuffer> {
        if let Some(buffer) = self.diff(state)? {
            Ok(buffer)
        } else {
            let buffer = self.doc.encode_update_v1()?;
            Ok(buffer.into())
        }
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
    pub fn off_update(&mut self) -> Result<()> {
        self.doc.unsubscribe_all();
        Ok(())
    }

    #[napi]
    pub fn destroy(&mut self) {
        if let Err(e) = self.off_update() {
            eprintln!("Failed to unsubscribe at doc destroy: {:?}", e);
        }
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
