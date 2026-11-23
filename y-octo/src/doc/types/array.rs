use super::*;

impl_type!(Array);

impl ListType for Array {}

/// The value at `index` of the array type `ty`. The caller holds the store
/// lock.
pub(crate) fn array_get(cx: TypeCx<'_>, ty: &YType, index: u64) -> Option<Value> {
    let (item, offset) = item_at(&cx.types.items, ty, index)?;
    item.and_then(|i| cx.types.items.get(i)).and_then(|item| {
        // TODO: rewrite to content.read(&mut [Any])
        match &item.content {
            Content::Any(any) => any.get(offset as usize).map(|any| Value::Any(any.clone())),
            _ => Some(Value::from_content(cx, &item.content)),
        }
    })
}

/// The values of an array type. The caller holds the store lock while
/// iterating.
pub(crate) fn array_values<'a>(cx: TypeCx<'a>, ty: &'a YType) -> impl Iterator<Item = Value> + 'a {
    ListIterator::new(&cx.types.items, ty)
        .filter(|item| item.countable())
        .flat_map(move |item| -> Box<dyn Iterator<Item = Value> + 'a> {
            match &item.content {
                Content::Any(any) if !any.is_empty() => Box::new(any.iter().cloned().map(Value::Any)),
                content => Box::new(std::iter::once(Value::from_content(cx, content))),
            }
        })
}

impl Array {
    #[inline(always)]
    pub fn id(&self) -> Option<Id> {
        self._id()
    }

    #[inline]
    pub fn len(&self) -> u64 {
        self.content_len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get(&self, index: u64) -> Option<Value> {
        let parent = self.as_inner();
        or_released(parent.read(|store, ty| array_get(parent.cx(store), ty, index)))
    }

    /// A snapshot of the values, taken under one store read lock.
    pub fn iter(&self) -> std::vec::IntoIter<Value> {
        let parent = self.as_inner();
        or_released(parent.read(|store, ty| array_values(parent.cx(store), ty).collect::<Vec<_>>())).into_iter()
    }

    pub fn push<V: Into<Value>>(&mut self, val: V) -> JwstCodecResult {
        self.push_value(val.into())
    }

    pub fn insert<V: Into<Value>>(&mut self, idx: u64, val: V) -> JwstCodecResult {
        self.insert_value_at(idx, val.into())
    }

    pub fn remove(&mut self, idx: u64, len: u64) -> JwstCodecResult {
        self.remove_at(idx, len)
    }
}

impl serde::Serialize for Array {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeSeq;

        let values = self.iter();
        let mut seq = serializer.serialize_seq(Some(values.len()))?;

        for item in values {
            seq.serialize_element(&item)?;
        }
        seq.end()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_yarray_insert() {
        let options = DocOptions::default();

        loom_model!({
            let doc = Doc::with_options(options.clone());
            let mut array = doc.get_or_create_array("abc").unwrap();

            array.insert(0, " ").unwrap();
            array.insert(0, "Hello").unwrap();
            array.insert(2, "World").unwrap();

            assert_eq!(array.get(0).unwrap(), Value::Any(Any::String("Hello".into())));
            assert_eq!(array.get(1).unwrap(), Value::Any(Any::String(" ".into())));
            assert_eq!(array.get(2).unwrap(), Value::Any(Any::String("World".into())));
        });
    }

    #[test]
    fn test_yarray_delete() {
        let options = DocOptions::default();

        loom_model!({
            let doc = Doc::with_options(options.clone());
            let mut array = doc.get_or_create_array("abc").unwrap();

            array.insert(0, " ").unwrap();
            array.insert(0, "Hello").unwrap();
            array.insert(2, "World").unwrap();
            array.remove(0, 2).unwrap();

            assert_eq!(array.get(0).unwrap(), Value::Any(Any::String("World".into())));
        });
    }

    #[test]
    fn test_yjs_text_as_sequence() {
        for fixture in ["text-split", "text-append"] {
            let update = crate::doc::yjs_fixture(fixture);
            loom_model!({
                let doc = Doc::try_from_binary_v1(&update).unwrap();
                let array = doc.get_or_create_array("abc").unwrap();
                let text = array
                    .iter()
                    .map(|v| match v {
                        Value::Any(Any::String(s)) => s,
                        _ => panic!("text sequence contains non-string"),
                    })
                    .collect::<String>();
                assert_eq!(text, "Hello World!");
                assert_eq!(array.len(), 12);
            });
        }
    }

    #[test]
    fn test_yjs_array_decode() {
        let update = crate::doc::yjs_fixture("array-words");
        loom_model!({
            let doc = Doc::try_from_binary_v1(&update).unwrap();
            let arr = doc.get_or_create_array("abc").unwrap();
            assert_eq!(arr.get(2).unwrap(), Value::Any(Any::String("world".to_string())));
            assert_eq!(arr.len(), 3);
        });
    }

    /// A type is inserted at most once: a second insert would rewrite its item
    /// while the first container still holds it, and the ancestor walk could
    /// then miss a cycle (a contains b, b moved under c, b takes a), which the
    /// recursive delete of `a` would walk with aliased `&mut` types.
    #[test]
    fn test_type_is_inserted_at_most_once() {
        loom_model!({
            let doc = Doc::with_client(1);
            let mut a = doc.create_array().unwrap();
            let mut b = doc.create_array().unwrap();
            let mut c = doc.get_or_create_array("c").unwrap();

            a.push(b.clone()).unwrap();
            assert_eq!(c.push(b.clone()), Err(JwstCodecError::TypeAlreadyInserted));
            assert_eq!(b.push(a.clone()), Err(JwstCodecError::InvalidParent));
            a.remove(0, 1).unwrap();

            // deleted and collected types stay inserted
            assert_eq!(a.push(b.clone()), Err(JwstCodecError::TypeAlreadyInserted));
            doc.gc().unwrap();
            assert_eq!(c.insert(0, b.clone()), Err(JwstCodecError::TypeAlreadyInserted));
            // so do root types
            assert_eq!(a.push(c.clone()), Err(JwstCodecError::TypeAlreadyInserted));

            assert!(a.is_empty());
            assert!(c.is_empty());
            assert!(b.is_empty());
        });
    }
}
