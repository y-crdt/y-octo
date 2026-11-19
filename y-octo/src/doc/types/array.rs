use super::*;

impl_type!(Array);

impl ListType for Array {}

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
        parent
            .read(|_, ty| {
                let (item, offset) = item_at(parent, ty, index)?;
                item.get().and_then(|item| {
                    // TODO: rewrite to content.read(&mut [Any])
                    match &item.content {
                        Content::Any(any) => any.get(offset as usize).map(|any| Value::Any(any.clone())),
                        _ => Some(Value::from(&item.content)),
                    }
                })
            })
            .ok()
            .flatten()
    }

    /// A snapshot of the values, taken under one store read lock.
    pub fn iter(&self) -> std::vec::IntoIter<Value> {
        self.as_inner()
            .read(|_, ty| {
                let mut values = Vec::with_capacity(ty.len as usize);
                for item in ListIterator::new(ty) {
                    if !item.countable() {
                        continue;
                    }
                    match &item.content {
                        Content::Any(any) if !any.is_empty() => values.extend(any.iter().cloned().map(Value::Any)),
                        _ => values.push(Value::from(&item.content)),
                    }
                }
                values
            })
            .unwrap_or_default()
            .into_iter()
    }

    pub fn push<V: Into<Value>>(&mut self, val: V) -> JwstCodecResult {
        self.push_back(val.into().into())
    }

    pub fn insert<V: Into<Value>>(&mut self, idx: u64, val: V) -> JwstCodecResult {
        self.insert_at(idx, val.into().into())
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
    #[cfg_attr(miri, ignore)]
    fn test_ytext_equal() {
        use yrs::{Options, Text, Transact};
        let options = DocOptions::default();
        let yrs_options = Options::default();

        loom_model!({
            let doc = yrs::Doc::with_options(yrs_options.clone());
            let array = doc.get_or_insert_text("abc");

            let mut trx = doc.transact_mut();
            array.insert(&mut trx, 0, " ");
            array.insert(&mut trx, 0, "Hello");
            array.insert(&mut trx, 6, "World");
            array.insert(&mut trx, 11, "!");
            let buffer = trx.encode_update_v1();

            let mut decoder = RawDecoder::new(&buffer);
            let update = Update::read(&mut decoder).unwrap();

            let mut doc = Doc::with_options(options.clone());
            doc.apply_update(update).unwrap();
            let array = doc.get_or_create_array("abc").unwrap();

            assert_eq!(array.get(0).unwrap(), Value::Any(Any::String("Hello".into())));
            assert_eq!(array.get(5).unwrap(), Value::Any(Any::String(" ".into())));
            assert_eq!(array.get(6).unwrap(), Value::Any(Any::String("World".into())));
            assert_eq!(array.get(11).unwrap(), Value::Any(Any::String("!".into())));
        });

        let options = DocOptions::default();
        let yrs_options = Options::default();

        loom_model!({
            let doc = yrs::Doc::with_options(yrs_options.clone());
            let array = doc.get_or_insert_text("abc");

            let mut trx = doc.transact_mut();
            array.insert(&mut trx, 0, "Hello");
            array.insert(&mut trx, 5, " ");
            array.insert(&mut trx, 6, "World");
            array.insert(&mut trx, 11, "!");
            let buffer = trx.encode_update_v1();

            let mut decoder = RawDecoder::new(&buffer);
            let update = Update::read(&mut decoder).unwrap();

            let mut doc = Doc::with_options(options.clone());
            doc.apply_update(update).unwrap();
            let array = doc.get_or_create_array("abc").unwrap();

            assert_eq!(array.get(0).unwrap(), Value::Any(Any::String("Hello".into())));
            assert_eq!(array.get(5).unwrap(), Value::Any(Any::String(" ".into())));
            assert_eq!(array.get(6).unwrap(), Value::Any(Any::String("World".into())));
            assert_eq!(array.get(11).unwrap(), Value::Any(Any::String("!".into())));
        });
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_yrs_array_decode() {
        use yrs::{Array, Transact};

        loom_model!({
            let update = {
                let doc = yrs::Doc::new();
                let array = doc.get_or_insert_array("abc");
                let mut trx = doc.transact_mut();

                array.insert(&mut trx, 0, "hello");
                array.insert(&mut trx, 1, "world");
                array.insert(&mut trx, 1, " ");

                trx.encode_update_v1()
            };
            let doc = Doc::try_from_binary_v1_with_options(
                update.clone(),
                DocOptions {
                    guid: String::from("1"),
                    client_id: 1,
                    gc: true,
                },
            )
            .unwrap();
            let arr = doc.get_or_create_array("abc").unwrap();

            assert_eq!(arr.get(2).unwrap(), Value::Any(Any::String("world".to_string())))
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
