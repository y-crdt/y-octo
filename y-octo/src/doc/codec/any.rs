use std::{
    fmt::{self, Display},
    ops::RangeInclusive,
};

use ordered_float::OrderedFloat;

use super::*;

const MAX_JS_INT: i64 = 0x001F_FFFF_FFFF_FFFF;
// The smallest int in js number.
const MIN_JS_INT: i64 = -MAX_JS_INT;
pub const JS_INT_RANGE: RangeInclusive<i64> = MIN_JS_INT..=MAX_JS_INT;

/// A JSON-like value stored in Yjs `ContentAny`, map entries, formats and
/// subdocument options, encoded like `lib0` `writeAny`.
///
/// Containers own their entries, so a value is a tree whose derived `Clone`,
/// `PartialEq` and `Debug`, drop and serde recurse once per nesting level.
/// Decoding therefore accepts at most [Any::DEFAULT_MAX_DEPTH] levels unless a
/// trusted caller raises the limit, up to [Any::MAX_CONFIGURABLE_DEPTH]; Yjs
/// itself puts no limit on the wire.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(fuzzing, derive(arbitrary::Arbitrary))]
#[cfg_attr(test, derive(proptest_derive::Arbitrary))]
pub enum Any {
    Undefined,
    Null,
    Integer(i32),
    Float32(OrderedFloat<f32>),
    Float64(OrderedFloat<f64>),
    BigInt64(i64),
    False,
    True,
    String(String),
    // FIXME: due to macro's overflow evaluating, we can't use proptest here
    #[cfg_attr(test, proptest(skip))]
    Object(Box<HashMap<String, Any>>),
    #[cfg_attr(test, proptest(skip))]
    Array(Vec<Any>),
    Binary(Vec<u8>),
}

impl<R: CrdtReader> CrdtRead<R> for Any {
    /// Reads one value nested at most [Any::DEFAULT_MAX_DEPTH] levels.
    fn read(reader: &mut R) -> JwstCodecResult<Self> {
        Self::read_with_max_depth(reader, Self::DEFAULT_MAX_DEPTH)
    }
}

/// What one tag starts: a complete value, or a container of `len` entries.
enum AnyHead {
    Value(Any),
    Array(usize),
    Object(usize),
}

/// A container being read: its entries so far and how many are left.
enum AnyFrame {
    Array(Vec<Any>, usize),
    /// entries, key of the value being read, entries left after it
    Object(HashMap<String, Any>, String, usize),
}

impl Any {
    /// Default nesting limit of every decoding entry point: [Any::read],
    /// [crate::Update::decode_v1], [crate::Doc::apply_update_from_binary_v1]
    /// and [crate::ReadLimits::default].
    ///
    /// The root value has depth 0 and each array element or object value is
    /// one deeper than its container. Yjs and `lib0` `readAny` put no limit on
    /// the wire; y-octo rejects deeper values from untrusted input because
    /// [Any] is an owned tree whose derived `Clone`, `PartialEq` and `Debug`,
    /// drop and serde use stack in proportion to its depth.
    pub const DEFAULT_MAX_DEPTH: usize = 128;

    /// Largest nesting limit the decoding entry points accept. Trusted callers
    /// can set a limit in `0..=MAX_CONFIGURABLE_DEPTH` with
    /// [Any::read_with_max_depth],
    /// [crate::Update::decode_v1_with_max_any_depth]
    /// or [crate::ReadLimits::max_any_depth]; larger limits act as this one.
    /// `Any` values nested deeper are not supported.
    pub const MAX_CONFIGURABLE_DEPTH: usize = 1_024;

    /// Reads one value nested at most `max_depth` levels, where `max_depth`
    /// above [Any::MAX_CONFIGURABLE_DEPTH] acts as that limit. A limit of 0
    /// accepts scalars and empty containers only. Deeper values fail with
    /// [JwstCodecError::IncompleteDocument]. Reading uses an explicit stack
    /// rather than recursion.
    ///
    /// ```
    /// use y_octo::{Any, CrdtRead, CrdtWrite, RawDecoder, RawEncoder};
    ///
    /// // 200 arrays nested around a null: deeper than the default limit
    /// let mut deep = Any::Null;
    /// for _ in 0..200 {
    ///     deep = Any::Array(vec![deep]);
    /// }
    /// let mut encoder = RawEncoder::default();
    /// deep.write(&mut encoder).unwrap();
    /// let bytes = encoder.into_inner();
    ///
    /// assert!(Any::read(&mut RawDecoder::new(&bytes)).is_err());
    /// let decoded = Any::read_with_max_depth(&mut RawDecoder::new(&bytes), 200).unwrap();
    /// assert_eq!(decoded, deep);
    /// ```
    pub fn read_with_max_depth<R: CrdtReader>(reader: &mut R, max_depth: usize) -> JwstCodecResult<Self> {
        let max_depth = max_depth.min(Self::MAX_CONFIGURABLE_DEPTH);
        let mut head = Self::read_head(reader)?;
        // open containers, outermost first; the next value is one deeper
        let mut stack: Vec<AnyFrame> = Vec::new();
        loop {
            let mut value = match head {
                AnyHead::Value(value) => value,
                AnyHead::Array(0) => Any::Array(Vec::new()),
                AnyHead::Object(0) => Any::Object(Box::default()),
                AnyHead::Array(len) => {
                    stack.push(AnyFrame::Array(Vec::with_capacity(len.min(HASHMAP_SAFE_CAPACITY)), len));
                    head = Self::read_nested_head(reader, stack.len(), max_depth)?;
                    continue;
                }
                AnyHead::Object(len) => {
                    let key = reader.read_var_string()?;
                    let entries = HashMap::with_capacity(len.min(HASHMAP_SAFE_CAPACITY));
                    stack.push(AnyFrame::Object(entries, key, len));
                    head = Self::read_nested_head(reader, stack.len(), max_depth)?;
                    continue;
                }
            };
            // store the finished value, closing every container it completes
            loop {
                let Some(frame) = stack.last_mut() else {
                    return Ok(value);
                };
                let done = match frame {
                    AnyFrame::Array(values, left) => {
                        values.push(value);
                        *left -= 1;
                        *left == 0
                    }
                    AnyFrame::Object(entries, key, left) => {
                        entries.insert(std::mem::take(key), value);
                        *left -= 1;
                        if *left > 0 {
                            *key = reader.read_var_string()?;
                        }
                        *left == 0
                    }
                };
                if !done {
                    break;
                }
                value = match stack.pop() {
                    Some(AnyFrame::Array(values, _)) => Any::Array(values),
                    Some(AnyFrame::Object(entries, ..)) => Any::Object(Box::new(entries)),
                    None => unreachable!("a frame was just inspected"),
                };
            }
            head = Self::read_nested_head(reader, stack.len(), max_depth)?;
        }
    }

    fn read_nested_head<R: CrdtReader>(reader: &mut R, depth: usize, max_depth: usize) -> JwstCodecResult<AnyHead> {
        if depth > max_depth {
            return Err(JwstCodecError::IncompleteDocument(format!(
                "Any nesting deeper than {max_depth}"
            )));
        }
        Self::read_head(reader)
    }

    fn read_head<R: CrdtReader>(reader: &mut R) -> JwstCodecResult<AnyHead> {
        let index = reader.read_u8()?;
        let value = match 127u8.overflowing_sub(index).0 {
            0 => Any::Undefined,
            1 => Any::Null,
            // in yjs implementation, flag 2 only save 32bit integer
            2 => {
                let (value, negative) = reader.read_var_i32_with_sign()?;
                // Yjs can encode -0 with the integer tag; use a float to retain
                // its sign.
                if value == 0 && negative {
                    Any::Float32((-0.0_f32).into())
                } else {
                    Any::Integer(value)
                }
            }
            3 => Any::Float32(reader.read_f32_be()?.into()), // Float32
            4 => Any::Float64(reader.read_f64_be()?.into()), // Float64
            5 => Any::BigInt64(reader.read_i64_be()?),       // BigInt64
            6 => Any::False,
            7 => Any::True,
            8 => Any::String(reader.read_var_string()?), // String
            // each object entry takes at least a key length and a value tag
            9 => return Ok(AnyHead::Object(Self::read_len(reader, 2)?)),
            // each array element takes at least its tag
            10 => return Ok(AnyHead::Array(Self::read_len(reader, 1)?)),
            11 => Any::Binary(reader.read_var_buffer()?.to_vec()), // Binary
            // lib0 `readAny` fails on unknown tags too
            tag => return Err(JwstCodecError::IncompleteDocument(format!("unknown Any tag: {tag}"))),
        };
        Ok(AnyHead::Value(value))
    }

    /// Reads a container length the rest of the input can hold when every
    /// entry takes at least `min_bytes`.
    fn read_len<R: CrdtReader>(reader: &mut R, min_bytes: u64) -> JwstCodecResult<usize> {
        let len = reader.read_var_u64()?;
        if len > reader.len() / min_bytes {
            return Err(JwstCodecError::IncompleteDocument(format!(
                "Any container declares {len} entries beyond the input"
            )));
        }
        usize::try_from(len).map_err(|_| JwstCodecError::IncompleteDocument("Any container too large".into()))
    }
}

impl<W: CrdtWriter> CrdtWrite<W> for Any {
    /// Writes the value like `lib0` `writeAny`. Nested containers are written
    /// with an explicit stack rather than recursion.
    fn write(&self, writer: &mut W) -> JwstCodecResult {
        self.write_head(writer)?;
        match self {
            Any::Array(values) if !values.iter().any(Any::is_container) => {
                values.iter().try_for_each(|value| value.write_head(writer))
            }
            Any::Object(entries) if !entries.values().any(Any::is_container) => {
                entries.iter().try_for_each(|(key, value)| {
                    writer.write_var_string(key)?;
                    value.write_head(writer)
                })
            }
            Any::Array(_) | Any::Object(_) => self.write_nested(writer),
            _ => Ok(()),
        }
    }
}

/// Entries of a container still to be written.
enum WriteFrame<'a> {
    Array(std::slice::Iter<'a, Any>),
    Object(std::collections::hash_map::Iter<'a, String, Any>),
}

impl Any {
    fn is_container(&self) -> bool {
        matches!(self, Any::Array(_) | Any::Object(_))
    }

    /// Writes the entries of a container whose head is already written.
    fn write_nested<W: CrdtWriter>(&self, writer: &mut W) -> JwstCodecResult {
        let mut stack = Vec::new();
        Self::push_entries(self, &mut stack);
        while let Some(frame) = stack.last_mut() {
            let next = match frame {
                WriteFrame::Array(values) => values.next(),
                WriteFrame::Object(entries) => match entries.next() {
                    Some((key, value)) => {
                        writer.write_var_string(key)?;
                        Some(value)
                    }
                    None => None,
                },
            };
            match next {
                Some(value) => {
                    value.write_head(writer)?;
                    Self::push_entries(value, &mut stack);
                }
                None => {
                    stack.pop();
                }
            }
        }
        Ok(())
    }

    fn push_entries<'a>(value: &'a Any, stack: &mut Vec<WriteFrame<'a>>) {
        match value {
            Any::Array(values) => stack.push(WriteFrame::Array(values.iter())),
            Any::Object(entries) => stack.push(WriteFrame::Object(entries.iter())),
            _ => {}
        }
    }

    /// Writes a scalar completely, or the tag and length of a container.
    fn write_head<W: CrdtWriter>(&self, writer: &mut W) -> JwstCodecResult {
        match self {
            Any::Undefined => writer.write_u8(127)?,
            Any::Null => writer.write_u8(127 - 1)?,
            Any::Integer(value) => {
                writer.write_u8(127 - 2)?;
                writer.write_var_i32(*value)?;
            }
            Any::Float32(value) => {
                writer.write_u8(127 - 3)?;
                writer.write_f32_be(value.into_inner())?;
            }
            Any::Float64(value) => {
                writer.write_u8(127 - 4)?;
                writer.write_f64_be(value.into_inner())?;
            }
            Any::BigInt64(value) => {
                writer.write_u8(127 - 5)?;
                writer.write_i64_be(*value)?;
            }
            Any::False => writer.write_u8(127 - 6)?,
            Any::True => writer.write_u8(127 - 7)?,
            Any::String(value) => {
                writer.write_u8(127 - 8)?;
                writer.write_var_string(value)?;
            }
            Any::Object(entries) => {
                writer.write_u8(127 - 9)?;
                writer.write_var_u64(entries.len() as u64)?;
            }
            Any::Array(values) => {
                writer.write_u8(127 - 10)?;
                writer.write_var_u64(values.len() as u64)?;
            }
            Any::Binary(value) => {
                writer.write_u8(127 - 11)?;
                writer.write_var_buffer(value)?;
            }
        }

        Ok(())
    }

    pub(crate) fn write_multiple<W: CrdtWriter>(writer: &mut W, any: &[Any]) -> JwstCodecResult {
        writer.write_var_u64(any.len() as u64)?;
        for value in any {
            value.write(writer)?;
        }

        Ok(())
    }
}

macro_rules! impl_primitive_from {
    (unsigned, $($ty: ty),*) => {
        $(
            impl From<$ty> for Any {
                fn from(value: $ty) -> Self {
                    // INFO: i64::MAX > value > u64::MAX will cut down
                    // yjs binary does not consider the case that the int size exceeds i64
                    let int: i64 = value as i64;
                    // handle the behavior same as yjs
                    if JS_INT_RANGE.contains(&int) {
                        if int <= i32::MAX as i64 {
                            Self::Integer(int as i32)
                        } else if int as f32 as i64 == int {
                            Self::Float32((int as f32).into())
                        } else {
                            Self::Float64((int as f64).into())
                        }
                    } else {
                        Self::BigInt64(int)
                    }
                }
            }
        )*
    };
    (signed, $($ty: ty),*) => {
        $(
            impl From<$ty> for Any {
                fn from(value: $ty) -> Self {
                    let int: i64 = value.into();
                    // handle the behavior same as yjs
                    if JS_INT_RANGE.contains(&int) {
                        if int <= i32::MAX as i64 {
                            Self::Integer(int as i32)
                        } else if int as f32 as i64 == int {
                            Self::Float32((int as f32).into())
                        } else {
                            Self::Float64((int as f64).into())
                        }
                    } else {
                        Self::BigInt64(int)
                    }
                }
            }
        )*
    };
    (string, $($ty: ty),*) => {
        $(
            impl From<$ty> for Any {
                fn from(value: $ty) -> Self {
                    Self::String(value.into())
                }
            }
        )*
    };
}

impl_primitive_from!(unsigned, u8, u16, u32, u64);
impl_primitive_from!(signed, i8, i16, i32, i64);
impl_primitive_from!(string, String, &str);

impl From<usize> for Any {
    fn from(value: usize) -> Self {
        (value as u64).into()
    }
}

impl From<isize> for Any {
    fn from(value: isize) -> Self {
        (value as i64).into()
    }
}

impl From<f32> for Any {
    fn from(value: f32) -> Self {
        Self::Float32(value.into())
    }
}

impl From<f64> for Any {
    fn from(value: f64) -> Self {
        if value.trunc() == value {
            (value as i64).into()
        } else if value as f32 as f64 == value {
            Self::Float32((value as f32).into())
        } else {
            Self::Float64(value.into())
        }
    }
}

impl From<bool> for Any {
    fn from(value: bool) -> Self {
        if value { Self::True } else { Self::False }
    }
}

impl TryFrom<Any> for String {
    type Error = JwstCodecError;

    fn try_from(value: Any) -> Result<Self, Self::Error> {
        match value {
            Any::String(s) => Ok(s),
            _ => Err(JwstCodecError::UnexpectedType("String")),
        }
    }
}

impl TryFrom<Any> for HashMap<String, Any> {
    type Error = JwstCodecError;

    fn try_from(value: Any) -> Result<Self, Self::Error> {
        match value {
            Any::Object(map) => Ok(*map),
            _ => Err(JwstCodecError::UnexpectedType("Object")),
        }
    }
}

impl TryFrom<Any> for Vec<Any> {
    type Error = JwstCodecError;

    fn try_from(value: Any) -> Result<Self, Self::Error> {
        match value {
            Any::Array(vec) => Ok(vec),
            _ => Err(JwstCodecError::UnexpectedType("Array")),
        }
    }
}

impl TryFrom<Any> for bool {
    type Error = JwstCodecError;

    fn try_from(value: Any) -> Result<Self, Self::Error> {
        match value {
            Any::True => Ok(true),
            Any::False => Ok(false),
            _ => Err(JwstCodecError::UnexpectedType("Boolean")),
        }
    }
}

impl FromIterator<Any> for Any {
    fn from_iter<I: IntoIterator<Item = Any>>(iter: I) -> Self {
        Self::Array(iter.into_iter().collect())
    }
}

impl<'a> FromIterator<&'a Any> for Any {
    fn from_iter<I: IntoIterator<Item = &'a Any>>(iter: I) -> Self {
        Self::Array(iter.into_iter().cloned().collect())
    }
}

impl FromIterator<(String, Any)> for Any {
    fn from_iter<I: IntoIterator<Item = (String, Any)>>(iter: I) -> Self {
        let mut map = HashMap::new();
        map.extend(iter);
        Self::Object(Box::new(map))
    }
}

impl From<HashMap<String, Any>> for Any {
    fn from(value: HashMap<String, Any>) -> Self {
        Self::Object(Box::new(value))
    }
}

impl From<Vec<u8>> for Any {
    fn from(value: Vec<u8>) -> Self {
        Self::Binary(value)
    }
}

impl From<&[u8]> for Any {
    fn from(value: &[u8]) -> Self {
        Self::Binary(value.into())
    }
}

// TODO: impl for Any::Undefined
impl<T: Into<Any>> From<Option<T>> for Any {
    fn from(value: Option<T>) -> Self {
        if let Some(val) = value { val.into() } else { Any::Null }
    }
}

#[cfg(feature = "serde_json")]
impl From<serde_json::Value> for Any {
    fn from(value: serde_json::Value) -> Self {
        match value {
            serde_json::Value::Null => Self::Null,
            serde_json::Value::Bool(b) => {
                if b {
                    Self::True
                } else {
                    Self::False
                }
            }
            serde_json::Value::Number(n) => {
                if n.is_f64() {
                    Self::Float64(n.as_f64().unwrap().into())
                } else if n.is_i64() {
                    Self::Integer(n.as_i64().unwrap() as i32)
                } else {
                    Self::Integer(n.as_u64().unwrap() as i32)
                }
            }
            serde_json::Value::String(s) => Self::String(s),
            serde_json::Value::Array(vec) => Self::Array(vec.into_iter().map(|v| v.into()).collect::<Vec<_>>()),
            serde_json::Value::Object(obj) => {
                Self::Object(Box::new(obj.into_iter().map(|(k, v)| (k, v.into())).collect()))
            }
        }
    }
}

impl<'de> serde::Deserialize<'de> for Any {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::{Error, MapAccess, SeqAccess, Visitor};
        struct ValueVisitor;

        impl<'de> Visitor<'de> for ValueVisitor {
            type Value = Any;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("any valid JSON value")
            }

            #[inline]
            fn visit_bool<E>(self, value: bool) -> Result<Any, E> {
                Ok(if value { Any::True } else { Any::False })
            }

            #[inline]
            fn visit_i64<E>(self, value: i64) -> Result<Any, E> {
                Ok(Any::BigInt64(value))
            }

            #[inline]
            fn visit_u64<E>(self, value: u64) -> Result<Any, E> {
                Ok((value as i64).into())
            }

            #[inline]
            fn visit_f64<E>(self, value: f64) -> Result<Any, E> {
                Ok(Any::Float64(OrderedFloat(value)))
            }

            #[inline]
            fn visit_str<E>(self, value: &str) -> Result<Any, E>
            where
                E: Error,
            {
                self.visit_string(String::from(value))
            }

            #[inline]
            fn visit_string<E>(self, value: String) -> Result<Any, E> {
                Ok(Any::String(value))
            }

            #[inline]
            fn visit_none<E>(self) -> Result<Any, E> {
                Ok(Any::Null)
            }

            #[inline]
            fn visit_some<D>(self, deserializer: D) -> Result<Any, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                serde::Deserialize::deserialize(deserializer)
            }

            #[inline]
            fn visit_unit<E>(self) -> Result<Any, E> {
                Ok(Any::Null)
            }

            #[inline]
            fn visit_seq<V>(self, mut visitor: V) -> Result<Any, V::Error>
            where
                V: SeqAccess<'de>,
            {
                let mut vec = Vec::new();

                while let Some(elem) = visitor.next_element()? {
                    vec.push(elem);
                }

                Ok(Any::Array(vec))
            }

            fn visit_map<V>(self, mut visitor: V) -> Result<Any, V::Error>
            where
                V: MapAccess<'de>,
            {
                match visitor.next_key::<String>()? {
                    Some(k) => {
                        let mut values = HashMap::new();

                        values.insert(k, visitor.next_value()?);
                        while let Some((key, value)) = visitor.next_entry()? {
                            values.insert(key, value);
                        }

                        Ok(Any::Object(Box::new(values)))
                    }
                    None => Ok(Any::Object(Box::default())),
                }
            }
        }

        deserializer.deserialize_any(ValueVisitor)
    }
}

impl serde::Serialize for Any {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::{SerializeMap, SerializeSeq};

        match self {
            Any::Null => serializer.serialize_none(),
            Any::Undefined => serializer.serialize_none(),
            Any::True => serializer.serialize_bool(true),
            Any::False => serializer.serialize_bool(false),
            Any::Float32(value) => serializer.serialize_f32(value.0),
            Any::Float64(value) => serializer.serialize_f64(value.0),
            Any::Integer(value) => serializer.serialize_i32(*value),
            Any::BigInt64(value) => serializer.serialize_i64(*value),
            Any::String(value) => serializer.serialize_str(value.as_ref()),
            Any::Array(values) => {
                let mut seq = serializer.serialize_seq(Some(values.len()))?;
                for value in values.iter() {
                    seq.serialize_element(value)?;
                }
                seq.end()
            }
            Any::Object(entries) => {
                let mut map = serializer.serialize_map(Some(entries.len()))?;
                for (key, value) in entries.iter() {
                    map.serialize_entry(key, value)?;
                }
                map.end()
            }
            Any::Binary(buf) => serializer.serialize_bytes(buf),
        }
    }
}

impl Display for Any {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::True => write!(f, "true"),
            Self::False => write!(f, "false"),
            Self::String(s) => write!(f, "\"{s}\""),
            Self::Integer(i) => write!(f, "{i}"),
            Self::Float32(v) => write!(f, "{v}"),
            Self::Float64(v) => write!(f, "{v}"),
            Self::BigInt64(v) => write!(f, "{v}"),
            Self::Object(map) => {
                write!(f, "{{")?;
                for (i, (key, value)) in map.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{key}: {value}")?;
                }
                write!(f, "}}")
            }
            Self::Array(vec) => {
                write!(f, "[")?;
                for (i, value) in vec.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{value}")?;
                }
                write!(f, "]")
            }
            Self::Binary(buf) => write!(f, "{buf:?}"),
            Self::Undefined => write!(f, "undefined"),
            Self::Null => write!(f, "null"),
        }
    }
}

#[cfg(test)]
mod tests {
    use proptest::{collection::vec, prelude::*};

    use super::*;

    #[test]
    fn test_any_codec() {
        #[cfg(target_pointer_width = "64")]
        assert_eq!(std::mem::size_of::<Any>(), 32);

        let any = Any::Object(Box::new(
            vec![
                ("name".to_string(), Any::String("Alice".to_string())),
                ("age".to_string(), Any::Integer(25)),
                (
                    "contacts".to_string(),
                    Any::Array(vec![
                        Any::Object(Box::new(
                            vec![
                                ("type".to_string(), Any::String("Mobile".to_string())),
                                ("number".to_string(), Any::String("1234567890".to_string())),
                            ]
                            .into_iter()
                            .collect(),
                        )),
                        Any::Object(Box::new(
                            vec![
                                ("type".to_string(), Any::String("Email".to_string())),
                                ("address".to_string(), Any::String("alice@example.com".to_string())),
                            ]
                            .into_iter()
                            .collect(),
                        )),
                        Any::Undefined,
                    ]),
                ),
                (
                    "standard_data".to_string(),
                    Any::Array(vec![
                        Any::Undefined,
                        Any::Null,
                        Any::Integer(114514),
                        Any::Float32(114.514.into()),
                        Any::Float64(115.514.into()),
                        Any::BigInt64(-1145141919810),
                        Any::False,
                        Any::True,
                        Any::Object(Box::new(
                            vec![
                                ("name".to_string(), Any::String("tadokoro".to_string())),
                                ("age".to_string(), Any::String("24".to_string())),
                                ("profession".to_string(), Any::String("student".to_string())),
                            ]
                            .into_iter()
                            .collect(),
                        )),
                        Any::Binary(vec![1, 2, 3, 4, 5]),
                    ]),
                ),
            ]
            .into_iter()
            .collect(),
        ));

        let mut encoder = RawEncoder::default();
        any.write(&mut encoder).unwrap();
        let encoded = encoder.into_inner();

        let mut decoder = RawDecoder::new(&encoded);
        let decoded = Any::read(&mut decoder).unwrap();

        assert_eq!(any, decoded);

        for bytes in [&[125, 64][..], &[124, 128, 0, 0, 0], &[123, 128, 0, 0, 0, 0, 0, 0, 0]] {
            let decoded = Any::read(&mut RawDecoder::new(bytes)).unwrap();
            assert!(match &decoded {
                Any::Float32(value) => value.0 == 0.0 && value.0.is_sign_negative(),
                Any::Float64(value) => value.0 == 0.0 && value.0.is_sign_negative(),
                _ => false,
            });
            let mut encoder = RawEncoder::default();
            decoded.write(&mut encoder).unwrap();
            assert_eq!(encoder.into_inner()[1], 128);
        }

        loom_model!({
            // Yjs 13.6.21 encodes this map's -0 as an integer with the sign
            // bit.
            let bytes = [1, 1, 1, 0, 40, 1, 1, 114, 1, 120, 1, 125, 64, 0];
            let update = Update::decode_v1(bytes).unwrap();
            let update = Update::decode_v1(Update::merge([update]).encode_v1().unwrap()).unwrap();
            let item = update.structs[&1][0].as_item();
            let Content::Any(values) = &item.get().unwrap().content else {
                panic!("expected ContentAny");
            };
            assert!(matches!(&values[0], Any::Float32(value) if value.0 == 0.0 && value.0.is_sign_negative()));
        });
    }

    proptest! {
        #[test]
        #[cfg_attr(miri, ignore)]
        fn test_random_any(any in vec(any::<Any>(), 0..100)) {
            for any in &any {
                let mut encoder = RawEncoder::default();
                any.write(&mut encoder).unwrap();
                let encoded = encoder.into_inner();

                let mut decoder = RawDecoder::new(&encoded);
                let decoded = Any::read(&mut decoder).unwrap();

                assert_eq!(any, &decoded);
            }
        }
    }

    #[test]
    fn test_convert_to_any() {
        let any: Vec<Any> = vec![
            42u8.into(),
            42u16.into(),
            42u32.into(),
            42u64.into(),
            114.514f32.into(),
            1919.810f64.into(),
            (-42i8).into(),
            (-42i16).into(),
            (-42i32).into(),
            (-42i64).into(),
            false.into(),
            true.into(),
            "JWST".to_string().into(),
            "OctoBase".into(),
            vec![1u8, 9, 1, 9].into(),
            (&[8u8, 1, 0][..]).into(),
            [Any::True, 42u8.into()].iter().collect(),
        ];
        assert_eq!(
            any,
            vec![
                Any::Integer(42),
                Any::Integer(42),
                Any::Integer(42),
                Any::Integer(42),
                Any::Float32(114.514.into()),
                Any::Float64(1919.810.into()),
                Any::Integer(-42),
                Any::Integer(-42),
                Any::Integer(-42),
                Any::Integer(-42),
                Any::False,
                Any::True,
                Any::String("JWST".to_string()),
                Any::String("OctoBase".to_string()),
                Any::Binary(vec![1, 9, 1, 9]),
                Any::Binary(vec![8, 1, 0]),
                Any::Array(vec![Any::True, Any::Integer(42)])
            ]
        );

        assert_eq!(
            vec![("key".to_string(), 10u64.into())].into_iter().collect::<Any>(),
            Any::Object(Box::new(HashMap::from_iter(vec![(
                "key".to_string(),
                Any::Integer(10)
            )])))
        );

        let any: Any = 10u64.into();
        assert_eq!([any].iter().collect::<Any>(), Any::Array(vec![Any::Integer(10)]));
    }

    /// `depth` arrays nested around a single null.
    fn nested_arrays(depth: usize) -> Vec<u8> {
        let mut bytes = [117u8, 1].repeat(depth);
        bytes.push(126);
        bytes
    }

    #[test]
    fn test_any_read_rejects_malformed() {
        // nesting at the limit decodes, one more level does not
        let decoded = Any::read(&mut RawDecoder::new(&nested_arrays(Any::DEFAULT_MAX_DEPTH))).unwrap();
        let mut encoder = RawEncoder::default();
        decoded.write(&mut encoder).unwrap();
        assert_eq!(encoder.into_inner(), nested_arrays(Any::DEFAULT_MAX_DEPTH));
        assert!(matches!(
            Any::read(&mut RawDecoder::new(&nested_arrays(Any::DEFAULT_MAX_DEPTH + 1))),
            Err(JwstCodecError::IncompleteDocument(_))
        ));
        // explicit limits still apply, in both directions
        assert!(Any::read_with_max_depth(&mut RawDecoder::new(&nested_arrays(3)), 2).is_err());
        assert!(Any::read_with_max_depth(&mut RawDecoder::new(&nested_arrays(200)), 200).is_ok());
        // raised limits stop at the configurable maximum
        let max = Any::MAX_CONFIGURABLE_DEPTH;
        assert!(Any::read_with_max_depth(&mut RawDecoder::new(&nested_arrays(max)), usize::MAX).is_ok());
        assert!(matches!(
            Any::read_with_max_depth(&mut RawDecoder::new(&nested_arrays(max + 1)), usize::MAX),
            Err(JwstCodecError::IncompleteDocument(message)) if message == "Any nesting deeper than 1024"
        ));

        // unknown tags fail like lib0 instead of decoding as undefined
        assert!(matches!(
            Any::read(&mut RawDecoder::new(&[100])),
            Err(JwstCodecError::IncompleteDocument(message)) if message == "unknown Any tag: 27"
        ));

        // lengths beyond the input fail before anything is allocated for them
        for tag in [117u8, 118] {
            let bytes = [tag, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01];
            assert!(matches!(
                Any::read(&mut RawDecoder::new(&bytes)),
                Err(JwstCodecError::IncompleteDocument(_))
            ));
        }
    }
}
