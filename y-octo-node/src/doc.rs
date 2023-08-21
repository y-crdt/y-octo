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
}
