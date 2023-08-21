use y_octo::Doc as YDoc;

use super::*;

#[napi]
pub struct Doc {
    doc: YDoc,
}

#[napi]
impl Doc {
    // #[napi(constructor)]
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
    pub fn get_or_create_text(&mut self, key: String) -> Result<Text> {
        self.doc
            .get_or_create_text(&key)
            .map(Text::new)
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
    fn test_create_text() {
        let mut doc = Doc::new(None);
        let text = doc.get_or_create_text("text".into()).unwrap();
        assert_eq!(text.len(), 0);
    }

    #[test]
    fn test_keys() {
        let mut doc = Doc::new(None);
        doc.get_or_create_text("text".into()).unwrap();
        assert_eq!(doc.keys(), vec!["text"]);
    }
}
