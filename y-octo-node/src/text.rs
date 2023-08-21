use y_octo::Text;

use super::*;

#[napi]
pub struct YText {
    pub(crate) text: Text,
}

#[napi]
impl YText {
    pub(crate) fn new(text: Text) -> Self {
        Self { text }
    }

    #[napi(getter)]
    pub fn len(&self) -> i64 {
        self.text.len() as i64
    }

    #[napi(getter)]
    pub fn is_empty(&self) -> bool {
        self.text.is_empty()
    }

    #[napi]
    pub fn insert(&mut self, char_index: i64, str: String) -> Result<()> {
        self.text
            .insert(char_index as u64, str)
            .map_err(|e| anyhow::Error::from(e))
    }

    #[napi]
    pub fn remove(&mut self, char_index: i64, len: i64) -> Result<()> {
        self.text
            .remove(char_index as u64, len as u64)
            .map_err(|e| anyhow::Error::from(e))
    }

    #[napi]
    pub fn to_string(&self) -> String {
        self.text.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_text_init() {
        let mut doc = Doc::new(None);
        let text = doc.get_or_create_text("text".into()).unwrap();
        assert_eq!(text.len(), 0);
    }

    #[test]
    fn test_text_edit() {
        let mut doc = Doc::new(None);
        let mut text = doc.get_or_create_text("text".into()).unwrap();
        text.insert(0, "hello".into()).unwrap();
        assert_eq!(text.to_string(), "hello");
        text.insert(5, " world".into()).unwrap();
        assert_eq!(text.to_string(), "hello world");
        text.remove(5, 6).unwrap();
        assert_eq!(text.to_string(), "hello");
    }
}
