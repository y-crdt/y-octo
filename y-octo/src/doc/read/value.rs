use std::{fmt, slice};

use super::{FrozenContent, FrozenValue, ReadDoc, TypeId};
use crate::{Any, TextAttributes, TextDeltaOp, TextInsert, YTypeKind, doc::utf16_offset_to_utf8};

#[derive(Clone, Copy)]
enum AnySource<'a> {
    Value(&'a Any),
    Slice(&'a [Any]),
    String(&'a str),
    Binary(&'a [u8]),
}

#[derive(Clone, Copy)]
pub struct ReadAny<'a>(AnySource<'a>);

impl<'a> ReadAny<'a> {
    fn value(value: &'a Any) -> Self {
        Self(AnySource::Value(value))
    }

    fn slice(value: &'a [Any]) -> Self {
        Self(AnySource::Slice(value))
    }

    fn string(value: &'a str) -> Self {
        Self(AnySource::String(value))
    }

    fn binary(value: &'a [u8]) -> Self {
        Self(AnySource::Binary(value))
    }

    /// Returns a borrowed string when this value is a string. O(1), no
    /// allocation.
    pub fn as_str(self) -> Option<&'a str> {
        match self.0 {
            AnySource::Value(Any::String(value)) => Some(value),
            AnySource::String(value) => Some(value),
            _ => None,
        }
    }

    /// Returns the boolean value when present. O(1), no allocation.
    pub fn as_bool(self) -> Option<bool> {
        match self.0 {
            AnySource::Value(Any::True) => Some(true),
            AnySource::Value(Any::False) => Some(false),
            _ => None,
        }
    }

    /// Returns an integer representation when present. O(1), no allocation.
    pub fn as_i64(self) -> Option<i64> {
        match self.0 {
            AnySource::Value(Any::Integer(value)) => Some(i64::from(*value)),
            AnySource::Value(Any::BigInt64(value)) => Some(*value),
            _ => None,
        }
    }

    /// Returns a floating-point representation when numeric. O(1), no
    /// allocation.
    pub fn as_f64(self) -> Option<f64> {
        match self.0 {
            AnySource::Value(Any::Integer(value)) => Some(f64::from(*value)),
            AnySource::Value(Any::BigInt64(value)) => Some(*value as f64),
            AnySource::Value(Any::Float32(value)) => Some(f64::from(value.0)),
            AnySource::Value(Any::Float64(value)) => Some(value.0),
            _ => None,
        }
    }

    /// Tests for null in O(1) without allocating.
    pub fn is_null(self) -> bool {
        matches!(self.0, AnySource::Value(Any::Null))
    }

    /// Tests for undefined in O(1) without allocating.
    pub fn is_undefined(self) -> bool {
        matches!(self.0, AnySource::Value(Any::Undefined))
    }

    /// Returns borrowed binary data when present. O(1), no allocation.
    pub fn as_binary(self) -> Option<&'a [u8]> {
        match self.0 {
            AnySource::Value(Any::Binary(value)) => Some(value),
            AnySource::Binary(value) => Some(value),
            _ => None,
        }
    }

    /// Iterates an Any array in O(n) without allocating a result container.
    pub fn array(self) -> Option<impl Iterator<Item = ReadAny<'a>> + 'a> {
        match self.0 {
            AnySource::Value(Any::Array(values)) => Some(values.iter().map(ReadAny::value)),
            AnySource::Slice(values) => Some(values.iter().map(ReadAny::value)),
            _ => None,
        }
    }

    /// Iterates an Any object in O(n) without allocating a result container.
    pub fn object(self) -> Option<impl Iterator<Item = (&'a str, ReadAny<'a>)> + 'a> {
        match self.0 {
            AnySource::Value(Any::Object(values)) => {
                Some(values.iter().map(|(key, value)| (key.as_str(), ReadAny::value(value))))
            }
            _ => None,
        }
    }

    /// Looks up an Any object member with the backing map's expected O(1) cost.
    pub fn get(self, key: &str) -> Option<ReadAny<'a>> {
        match self.0 {
            AnySource::Value(Any::Object(values)) => values.get(key).map(ReadAny::value),
            _ => None,
        }
    }

    /// Copies this value and allocates in proportion to the copied subtree.
    pub fn to_owned(self) -> Any {
        match self.0 {
            AnySource::Value(value) => value.clone(),
            AnySource::Slice(values) => Any::Array(values.to_vec()),
            AnySource::String(value) => Any::String(value.to_string()),
            AnySource::Binary(value) => Any::Binary(value.to_vec()),
        }
    }
}

#[derive(Clone, Copy)]
pub struct ReadMap<'a> {
    doc: &'a ReadDoc,
    id: TypeId,
}

impl<'a> ReadMap<'a> {
    pub(super) fn new((doc, id): (&'a ReadDoc, TypeId)) -> Self {
        Self { doc, id }
    }

    /// Looks up a key in O(log n) after expected O(1) key interning lookup.
    pub fn get(self, key: &str) -> Option<ReadValue<'a>> {
        let key = self.doc.keys.find(&self.doc.input, key)?;
        let map = &self.doc.types[self.id as usize].map;
        let index = map.binary_search_by_key(&key, |(candidate, _)| *candidate).ok()?;
        Some(self.doc.value(&map[index].1))
    }

    /// Tests key presence in O(log n) after expected O(1) key interning lookup.
    pub fn contains_key(self, key: &str) -> bool {
        self.get(key).is_some()
    }

    /// Returns the entry count in O(1).
    pub fn len(self) -> usize {
        self.doc.types[self.id as usize].map.len()
    }

    /// Tests emptiness in O(1).
    pub fn is_empty(self) -> bool {
        self.len() == 0
    }

    /// Iterates entries in O(n) without allocating a result container.
    pub fn iter(self) -> impl Iterator<Item = (&'a str, ReadValue<'a>)> + 'a {
        self.doc.types[self.id as usize]
            .map
            .iter()
            .map(move |(key, value)| (self.doc.keys.str(&self.doc.input, *key), self.doc.value(value)))
    }

    /// Iterates keys in O(n) without allocating a result container.
    pub fn keys(self) -> impl Iterator<Item = &'a str> + 'a {
        self.iter().map(|(key, _)| key)
    }

    /// Iterates values in O(n) without allocating a result container.
    pub fn values(self) -> impl Iterator<Item = ReadValue<'a>> + 'a {
        self.iter().map(|(_, value)| value)
    }
}

#[derive(Clone, Copy)]
pub struct ReadArray<'a> {
    doc: &'a ReadDoc,
    id: TypeId,
}

impl<'a> ReadArray<'a> {
    pub(super) fn new((doc, id): (&'a ReadDoc, TypeId)) -> Self {
        Self { doc, id }
    }

    /// Returns the visible element count in O(1).
    pub fn len(self) -> u64 {
        self.doc.types[self.id as usize].len
    }

    /// Tests emptiness in O(1).
    pub fn is_empty(self) -> bool {
        self.len() == 0
    }

    /// Returns an element in O(index); use [`Self::iter`] for sequential
    /// access.
    pub fn get(self, index: u64) -> Option<ReadValue<'a>> {
        self.iter().nth(index.try_into().ok()?)
    }

    /// Iterates visible elements in O(n) without allocating a result container.
    pub fn iter(self) -> impl Iterator<Item = ReadValue<'a>> + 'a {
        ReadArrayIter {
            doc: self.doc,
            values: self.doc.types[self.id as usize].list.iter(),
            pending: None,
        }
    }
}

struct ReadArrayIter<'a> {
    doc: &'a ReadDoc,
    values: slice::Iter<'a, FrozenValue>,
    pending: Option<slice::Iter<'a, Any>>,
}

impl<'a> Iterator for ReadArrayIter<'a> {
    type Item = ReadValue<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(pending) = &mut self.pending {
                if let Some(value) = pending.next() {
                    return Some(ReadValue::Any(ReadAny::value(value)));
                }
                self.pending = None;
            }
            let value = self.values.next()?;
            match &value.content {
                FrozenContent::Any(range) => {
                    let values = &self.doc.any[range.start as usize..range.end as usize];
                    let mut iter = values.iter();
                    let first = iter.next()?;
                    self.pending = Some(iter);
                    return Some(ReadValue::Any(ReadAny::value(first)));
                }
                FrozenContent::Format { .. } => continue,
                _ => return Some(self.doc.value(value)),
            }
        }
    }
}

#[derive(Clone, Copy)]
pub struct ReadText<'a> {
    doc: &'a ReadDoc,
    id: TypeId,
}

impl<'a> ReadText<'a> {
    pub(super) fn new((doc, id): (&'a ReadDoc, TypeId)) -> Self {
        Self { doc, id }
    }

    /// Returns the visible UTF-16 length in O(1).
    pub fn len(self) -> u64 {
        self.doc.types[self.id as usize].len
    }

    /// Tests emptiness in O(1).
    pub fn is_empty(self) -> bool {
        self.len() == 0
    }

    /// Iterates frozen text runs in O(number of runs) without allocating.
    pub fn runs(self) -> impl Iterator<Item = ReadTextRun<'a>> + 'a {
        self.doc.types[self.id as usize]
            .list
            .iter()
            .filter_map(move |value| match &value.content {
                FrozenContent::String(span) => Some(ReadTextRun::Text(self.doc.string_segment(*span, value))),
                FrozenContent::Any(range) => Some(ReadTextRun::Embed(ReadAny::slice(
                    &self.doc.any[range.start as usize..range.end as usize],
                ))),
                FrozenContent::Binary(span) => Some(ReadTextRun::Embed(ReadAny::binary(span.bytes(&self.doc.input)))),
                FrozenContent::Format { key, value } => Some(ReadTextRun::Format {
                    key: key.str(&self.doc.input),
                    value: ReadAny::value(&self.doc.any[*value as usize]),
                }),
                _ => None,
            })
    }

    /// Materializes an owned delta, allocating for text and attribute values.
    pub fn to_delta(self) -> Vec<TextDeltaOp> {
        let mut attributes = TextAttributes::default();
        let mut delta = Vec::new();
        for run in self.runs() {
            let insert = match run {
                ReadTextRun::Text(text) => TextInsert::Text(text.to_string()),
                ReadTextRun::Embed(value) => {
                    let value = value.to_owned();
                    TextInsert::Embed(match value {
                        Any::Array(values) => values,
                        value => vec![value],
                    })
                }
                ReadTextRun::Format { key, value } => {
                    let value = value.to_owned();
                    if matches!(value, Any::Null | Any::Undefined) {
                        attributes.remove(key);
                    } else {
                        attributes.insert(key.to_string(), value);
                    }
                    continue;
                }
            };
            let format = (!attributes.is_empty()).then(|| attributes.clone());
            if let (
                Some(TextDeltaOp::Insert {
                    insert: TextInsert::Text(previous),
                    format: previous_format,
                }),
                TextInsert::Text(text),
            ) = (delta.last_mut(), &insert)
                && *previous_format == format
            {
                previous.push_str(text);
            } else {
                delta.push(TextDeltaOp::Insert { insert, format });
            }
        }
        delta
    }
}

impl fmt::Display for ReadText<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        for run in self.runs() {
            if let ReadTextRun::Text(text) = run {
                formatter.write_str(text)?;
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
pub enum ReadTextRun<'a> {
    Text(&'a str),
    Embed(ReadAny<'a>),
    Format { key: &'a str, value: ReadAny<'a> },
}

#[derive(Clone, Copy)]
pub enum ReadValue<'a> {
    Any(ReadAny<'a>),
    Array(ReadArray<'a>),
    Map(ReadMap<'a>),
    Text(ReadText<'a>),
    Xml {
        kind: YTypeKind,
        tag: Option<&'a str>,
        map: ReadMap<'a>,
        array: ReadArray<'a>,
    },
    Doc {
        guid: &'a str,
        options: ReadAny<'a>,
    },
}

impl<'a> ReadValue<'a> {
    /// Returns the Any projection in O(1) without allocating.
    pub fn as_any(self) -> Option<ReadAny<'a>> {
        match self {
            Self::Any(value) => Some(value),
            _ => None,
        }
    }

    /// Returns the map projection in O(1) without allocating.
    pub fn as_map(self) -> Option<ReadMap<'a>> {
        match self {
            Self::Map(value) => Some(value),
            _ => None,
        }
    }

    /// Returns the array projection in O(1) without allocating.
    pub fn as_array(self) -> Option<ReadArray<'a>> {
        match self {
            Self::Array(value) => Some(value),
            _ => None,
        }
    }

    /// Returns the text projection in O(1) without allocating.
    pub fn as_text(self) -> Option<ReadText<'a>> {
        match self {
            Self::Text(value) => Some(value),
            _ => None,
        }
    }
}

impl ReadDoc {
    fn value<'a>(&'a self, value: &'a FrozenValue) -> ReadValue<'a> {
        match &value.content {
            FrozenContent::Any(range) => {
                let values = &self.any[range.start as usize..range.end as usize];
                let any = if values.len() == 1 {
                    ReadAny::value(&values[0])
                } else {
                    ReadAny::slice(values)
                };
                ReadValue::Any(any)
            }
            FrozenContent::Binary(span) => ReadValue::Any(ReadAny::binary(span.bytes(&self.input))),
            FrozenContent::String(span) => ReadValue::Any(ReadAny::string(self.string_segment(*span, value))),
            FrozenContent::Format { .. } => unreachable!("format items are only exposed through ReadText::runs"),
            FrozenContent::Type(id) => {
                let ty = &self.types[*id as usize];
                match ty.kind {
                    YTypeKind::Array => ReadValue::Array(ReadArray { doc: self, id: *id }),
                    YTypeKind::Map => ReadValue::Map(ReadMap { doc: self, id: *id }),
                    YTypeKind::Text => ReadValue::Text(ReadText { doc: self, id: *id }),
                    kind => ReadValue::Xml {
                        kind,
                        tag: ty.tag.map(|tag| tag.str(&self.input)),
                        map: ReadMap { doc: self, id: *id },
                        array: ReadArray { doc: self, id: *id },
                    },
                }
            }
            FrozenContent::Doc { guid, options } => ReadValue::Doc {
                guid: guid.str(&self.input),
                options: ReadAny::value(&self.any[*options as usize]),
            },
        }
    }

    fn string_segment<'a>(&'a self, span: super::Span, value: &FrozenValue) -> &'a str {
        let text = span.str(&self.input);
        let start = utf16_offset_to_utf8(text, value.content_offset);
        let end = start + utf16_offset_to_utf8(&text[start..], value.len);
        &text[start..end]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::doc::HashMap;

    #[test]
    fn any_scalar_accessors() {
        let values = [
            Any::Null,
            Any::Undefined,
            Any::False,
            Any::True,
            Any::Integer(-42),
            Any::BigInt64(i64::MAX),
            Any::Float32(1.5.into()),
            Any::Float64((-0.25).into()),
            Any::String("hello 😀".into()),
            Any::Binary(vec![0, 159, 146, 150]),
            Any::Array(vec![Any::Integer(1), "two".into(), Any::True]),
            Any::Object(HashMap::from_iter([(
                "deep".into(),
                Any::Object(HashMap::from_iter([("leaf".into(), Any::Float64(0.5.into()))])),
            )])),
        ];
        let cases = [
            ("null", (|value| value.is_null()) as fn(ReadAny) -> bool),
            ("undefined", |value| value.is_undefined()),
            ("false", |value| value.as_bool() == Some(false)),
            ("true", |value| value.as_bool() == Some(true)),
            ("int", |value| value.as_i64() == Some(-42)),
            ("bigint", |value| value.as_i64() == Some(i64::MAX)),
            ("f32", |value| value.as_f64() == Some(1.5)),
            ("f64", |value| value.as_f64() == Some(-0.25)),
            ("string", |value| value.as_str() == Some("hello 😀")),
            ("binary", |value| value.as_binary() == Some(&[0, 159, 146, 150][..])),
            ("array", |value| value.array().is_some_and(|array| array.count() == 3)),
            ("object", |value| {
                value.get("deep").and_then(|deep| deep.get("leaf")).unwrap().as_f64() == Some(0.5)
            }),
        ];

        for ((name, check), value) in cases.into_iter().zip(&values) {
            assert!(check(ReadAny::value(value)), "{name}");
        }
    }
}
