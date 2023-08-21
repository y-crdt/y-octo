use y_octo::Text as YText;

use super::*;

#[napi]
pub struct Text {
    text: YText,
}

#[napi]
impl Text {
    // #[napi(constructor)]
    pub(crate) fn new(text: YText) -> Self {
        Self { text }
    }

    #[napi(getter)]
    pub fn len(&self) -> i64 {
        self.text.len() as i64
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
}
