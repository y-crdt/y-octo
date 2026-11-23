use super::{
    Any, AsInner, Content, Id, JwstCodecError, JwstCodecResult, ListIterator, Text, TextAttributes, TextInsert, YType,
    is_nullish,
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
        self.as_inner().read(|store, ty| {
            ty.identity(&store.type_arena.items)?;
            identity_runs(&store.type_arena.items, ty)
        })?
    }
}

/// The caller holds the store lock.
pub(crate) fn identity_runs(items: &crate::doc::ItemSpace, ty: &YType) -> JwstCodecResult<Vec<TextIdentityRun>> {
    {
        let mut runs = Vec::new();
        let mut attributes = TextAttributes::new();
        for item in ListIterator::new(items, ty) {
            let insert = match &item.content {
                Content::Format(format) => {
                    let (key, value) = (&format.key, &format.value);
                    if is_nullish(value) {
                        attributes.remove(key.as_str());
                    } else {
                        attributes.insert(key.to_string(), value.clone());
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
