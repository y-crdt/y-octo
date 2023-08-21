use y_octo::Doc as YDoc;

use super::*;

#[napi]
pub struct Doc {
    doc: YDoc,
}

#[napi]
impl Doc {
    #[napi(constructor)]
    pub fn new(client_id: Option<i64>) -> Self {
        Self {
            doc: if let Some(client_id) = client_id {
                YDoc::with_client(client_id as u64)
            } else {
                YDoc::default()
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
    pub fn keys(&self) -> Vec<String> {
        self.doc.keys()
    }

    #[napi]
    pub fn get_or_create_array(&self, key: String) -> Result<YArray> {
        self.doc
            .get_or_create_array(&key)
            .map(YArray::new)
            .map_err(|e| anyhow::Error::from(e))
    }

    #[napi]
    pub fn get_or_create_text(&self, key: String) -> Result<YText> {
        self.doc
            .get_or_create_text(&key)
            .map(YText::new)
            .map_err(|e| anyhow::Error::from(e))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_doc_client() {
        let client_id = 1;
        let doc = Doc::new(Some(client_id));
        assert_eq!(doc.client_id(), 1);
    }

    #[test]
    fn test_doc_guid() {
        let doc = Doc::new(None);
        assert_eq!(doc.guid().len(), 21);
    }

    #[test]
    fn test_create_array() {
        let doc = Doc::new(None);
        let array = doc.get_or_create_array("array".into()).unwrap();
        assert_eq!(array.len(), 0);
    }

    #[test]
    fn test_create_text() {
        let doc = Doc::new(None);
        let text = doc.get_or_create_text("text".into()).unwrap();
        assert_eq!(text.len(), 0);
    }

    #[test]
    fn test_keys() {
        let doc = Doc::new(None);
        doc.get_or_create_array("array".into()).unwrap();
        doc.get_or_create_text("text".into()).unwrap();
        assert_eq!(doc.keys(), vec!["array", "text"]);
    }
}
