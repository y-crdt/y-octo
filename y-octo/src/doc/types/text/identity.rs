use super::{
    Any, Content, Id, JwstCodecError, JwstCodecResult, ListType, Text, TextAttributes, TextInsert, is_nullish,
};

/// A visible content run with its original UTF-16 clock range.
/// Format items update attributes but do not occupy visible positions.
#[derive(Debug, Clone, PartialEq)]
pub struct TextIdentityRun {
    pub id: Id,
    pub insert: TextInsert,
    pub attributes: TextAttributes,
}

impl Text {
    /// Reads visible identities without exposing mutable store internals.
    /// Deleted content is absent; use the document delete set for causal
    /// checks.
    pub fn identity_runs(&self) -> JwstCodecResult<Vec<TextIdentityRun>> {
        let mut runs = Vec::new();
        let mut attributes = TextAttributes::new();
        for item_ref in self.iter_item() {
            let item = item_ref.get().ok_or(JwstCodecError::DocReleased)?;
            let insert = match &item.content {
                Content::Format { key, value } => {
                    if is_nullish(value) {
                        attributes.remove(key.as_str());
                    } else {
                        attributes.insert(key.to_string(), value.as_ref().clone());
                    }
                    continue;
                }
                Content::String(text) => TextInsert::Text(text.clone()),
                Content::Embed(value) => TextInsert::Embed(vec![value.as_ref().clone()]),
                Content::Any(values) => TextInsert::Embed(values.clone()),
                Content::Json(values) => TextInsert::Embed(
                    values
                        .iter()
                        .map(|value| value.as_ref().map(|s| Any::String(s.clone())).unwrap_or(Any::Undefined))
                        .collect(),
                ),
                Content::Binary(value) => TextInsert::Embed(vec![Any::Binary(value.clone())]),
                _ => return Err(JwstCodecError::InvalidStructType("text content")),
            };
            runs.push(TextIdentityRun {
                id: item.id,
                insert,
                attributes: attributes.clone(),
            });
        }
        Ok(runs)
    }
}
