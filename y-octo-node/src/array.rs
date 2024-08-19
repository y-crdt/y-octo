use std::{
    ops::DerefMut,
    sync::{Arc, RwLock},
};

use napi::{
    bindgen_prelude::{Array as JsArray, FromNapiValue},
    iterator::Generator,
    Env, JsFunction, JsUnknown, ValueType,
};
use y_octo::{Any, Array, Doc, JwstCodecResult, Value};

use super::*;

fn cannot_insert_nested_ytype() -> anyhow::Error {
    anyhow::Error::msg("Cannot insert nested y-type before current raw-type integrated")
}

#[derive(Clone)]
pub(crate) enum ManagedArray {
    YArray { array: Array, doc: Doc },
    JsArray(Vec<Any>),
}

impl TryFrom<JsArray> for ManagedArray {
    type Error = anyhow::Error;

    fn try_from(array: JsArray) -> Result<Self, Self::Error> {
        match array
            .coerce_to_object()
            .and_then(|o| o.get_array_length().map(|l| (o, l)))
        {
            Ok((object, length)) => {
                let mut array = vec![];
                for i in 0..length {
                    if let Ok(unknown) = object.get_element::<JsUnknown>(i) {
                        match get_any_from_js_unknown(unknown) {
                            Ok(any) => array.push(any),
                            Err(e) => {
                                return Err(
                                    anyhow::Error::new(e).context(format!("Failed to coerce value to any: {}", i))
                                )
                            }
                        }
                    }
                }
                Ok(Self::JsArray(array))
            }
            Err(e) => Err(anyhow::Error::new(e).context("Failed to coerce value to array")),
        }
    }
}

impl ManagedArray {
    fn integrate_to_ytype(&mut self, doc: &Doc) -> JwstCodecResult<Array> {
        match self {
            Self::YArray { array, .. } => Ok(array.clone()),
            Self::JsArray(array) => {
                let mut yarray = doc.create_array()?;
                for value in array {
                    yarray.push(value.clone())?;
                }
                *self = Self::YArray {
                    array: yarray.clone(),
                    doc: doc.clone(),
                };
                Ok(yarray)
            }
        }
    }

    fn doc(&self) -> Option<&Doc> {
        match self {
            Self::YArray { doc, .. } => Some(doc),
            Self::JsArray(_) => None,
        }
    }

    fn len(&self) -> u64 {
        match self {
            Self::YArray { array, .. } => array.len(),
            Self::JsArray(array) => array.len() as u64,
        }
    }

    fn is_empty(&self) -> bool {
        match self {
            Self::YArray { array, .. } => array.is_empty(),
            Self::JsArray(array) => array.is_empty(),
        }
    }

    fn get(&self, env: Env, index: i64) -> Result<MixedYType> {
        match self {
            Self::YArray { array, doc } => {
                if let Some(value) = array.get(index as u64) {
                    match value {
                        Value::Any(any) => get_js_unknown_from_any(env, any).map(MixedYType::D),
                        Value::Array(array) => Ok(MixedYType::A(YArray::inner_new(array, doc))),
                        Value::Map(map) => Ok(MixedYType::B(YMap::inner_new(map, doc))),
                        Value::Text(text) => Ok(MixedYType::C(YText::inner_new(text))),
                        _ => env.get_null().map(|v| v.into_unknown()).map(MixedYType::D),
                    }
                    .map_err(anyhow::Error::from)
                } else {
                    Ok(MixedYType::D(env.get_null()?.into_unknown()))
                }
            }
            Self::JsArray(array) => array
                .get(index as usize)
                .ok_or_else(|| anyhow::Error::msg("Failed to get value from array"))
                .and_then(|any| {
                    get_js_unknown_from_any(env, any.clone())
                        .map(MixedYType::D)
                        .map_err(anyhow::Error::from)
                }),
        }
    }

    fn iter(&self) -> Box<dyn Iterator<Item = Value> + '_> {
        match self {
            Self::YArray { array, .. } => Box::new(array.iter().map(|v| v.into())),
            Self::JsArray(array) => Box::new(array.iter().map(|v| Value::Any(v.clone()))),
        }
    }

    fn insert<V: Into<Value>>(&mut self, index: u64, value: V) -> Result<(), anyhow::Error> {
        match self {
            Self::YArray { array, .. } => array.insert(index, value).map_err(anyhow::Error::from),
            Self::JsArray(array) => match value.into() {
                Value::Any(any) => Ok(array.insert(index as usize, any)),
                Value::Array(_) | Value::Map(_) | Value::Text(_) => Err(cannot_insert_nested_ytype()),
                _ => Err(anyhow::Error::msg("Unsupported value type")),
            },
        }
    }

    fn remove(&mut self, index: u64, len: u64) -> Result<(), anyhow::Error> {
        match self {
            Self::YArray { array, .. } => array.remove(index, len).map_err(anyhow::Error::from),
            Self::JsArray(array) => {
                if index >= array.len() as u64 {
                    return Err(anyhow::Error::msg("Index out of bounds"));
                } else if index + len > array.len() as u64 {
                    return Err(anyhow::Error::msg("Length out of bounds"));
                } else if len == 0 {
                    return Ok(());
                }

                array.drain((index as usize)..(index + len) as usize);
                Ok(())
            }
        }
    }
}

#[napi]
#[derive(Clone)]
pub struct YArray {
    pub(crate) array: Arc<RwLock<ManagedArray>>,
}

#[napi]
impl YArray {
    pub(crate) fn inner_new(array: Array, doc: &Doc) -> Self {
        Self {
            array: Arc::new(RwLock::new(ManagedArray::YArray {
                array,
                doc: doc.clone(),
            })),
        }
    }

    #[napi]
    pub fn from(array: JsArray) -> Result<Self> {
        Ok(Self {
            array: Arc::new(RwLock::new(array.try_into()?)),
        })
    }

    pub(crate) fn integrate_to_ytype(&self, doc: &Doc) -> JwstCodecResult<Array> {
        self.array.write().unwrap().integrate_to_ytype(doc)
    }

    #[napi(getter)]
    pub fn length(&self) -> i64 {
        self.array.read().unwrap().len() as i64
    }

    #[napi(getter)]
    pub fn is_empty(&self) -> bool {
        self.array.read().unwrap().is_empty()
    }

    #[napi(ts_generic_types = "T = unknown", ts_return_type = "T")]
    pub fn get(&self, env: Env, index: i64) -> Result<MixedYType> {
        self.array.read().unwrap().get(env, index)
    }

    #[napi(ts_generic_types = "T = unknown", ts_return_type = "Array<T>")]
    pub fn slice(&self, env: Env, start: i64, end: Option<i64>) -> Result<JsArray> {
        let mut js_array = env.create_array(0)?;
        let end = end
            .map(|end| {
                if end.is_negative() {
                    self.length() + end
                } else {
                    let end = end - start;
                    if end.is_negative() {
                        0
                    } else {
                        end
                    }
                }
            })
            .unwrap_or(self.length() - start) as usize;
        let array = self.array.read().unwrap();
        let doc = array.doc();
        for value in array.iter().skip(start as usize).take(end) {
            js_array.insert(get_js_unknown_from_value(env, doc, value)?)?;
        }
        Ok(js_array)
    }

    #[napi(ts_generic_types = "T = unknown", ts_return_type = "Array<T>")]
    pub fn map(&self, env: Env, callback: JsFunction) -> Result<JsArray> {
        let mut js_array = env.create_array(0)?;
        let array = self.array.read().unwrap();
        let doc = array.doc();
        for value in array.iter() {
            let js_value = get_js_unknown_from_value(env, doc, value)?;
            let result = callback.call(None, &[js_value.into_unknown()])?;
            js_array.insert(result)?;
        }
        Ok(js_array)
    }

    #[napi(
        ts_args_type = "index: number, value: YArray | YMap | YText | boolean | number | string | Record<string, any> \
                        | null | undefined"
    )]
    pub fn insert(&mut self, index: i64, value: MixedRefYType) -> Result<()> {
        let mut this = self.array.write().unwrap();
        match value {
            MixedRefYType::A(array) => {
                if let ManagedArray::YArray { array: yarray, doc } = this.deref_mut() {
                    let array = array.integrate_to_ytype(doc).map_err(anyhow::Error::from)?;
                    yarray.insert(index as u64, array).map_err(anyhow::Error::from)
                } else {
                    Err(cannot_insert_nested_ytype())
                }
            }
            MixedRefYType::B(map) => this.insert(index as u64, map.map.clone()).map_err(anyhow::Error::from),
            MixedRefYType::C(text) => this
                .insert(index as u64, text.text.clone())
                .map_err(anyhow::Error::from),
            MixedRefYType::D(unknown) => match unknown.get_type() {
                Ok(value_type) => match value_type {
                    ValueType::Undefined | ValueType::Null => {
                        this.insert(index as u64, Any::Null).map_err(anyhow::Error::from)
                    }
                    ValueType::Boolean => match unknown.coerce_to_bool().and_then(|v| v.get_value()) {
                        Ok(boolean) => this.insert(index as u64, boolean).map_err(anyhow::Error::from),
                        Err(e) => Err(anyhow::Error::new(e).context("Failed to coerce value to boolean")),
                    },
                    ValueType::Number => match unknown.coerce_to_number().and_then(|v| v.get_double()) {
                        Ok(number) => this.insert(index as u64, number).map_err(anyhow::Error::from),
                        Err(e) => Err(anyhow::Error::new(e).context("Failed to coerce value to number")),
                    },
                    ValueType::String => {
                        match unknown
                            .coerce_to_string()
                            .and_then(|v| v.into_utf8())
                            .and_then(|s| s.as_str().map(|s| s.to_string()))
                        {
                            Ok(string) => this.insert(index as u64, string).map_err(anyhow::Error::from),
                            Err(e) => Err(anyhow::Error::new(e).context("Failed to coerce value to string")),
                        }
                    }
                    ValueType::Object => match unknown
                        .coerce_to_object()
                        .and_then(|o| o.get_array_length().map(|l| (o, l)))
                    {
                        Ok((object, length)) => {
                            drop(this);
                            for i in 0..length {
                                if let Ok(unknown) = object.get_element::<JsUnknown>(i) {
                                    self.insert(index + i as i64, MixedRefYType::from_unknown(unknown)?)?;
                                }
                            }
                            Ok(())
                        }
                        Err(e) => Err(anyhow::Error::new(e).context("Failed to coerce value to object")),
                    },
                    ValueType::Symbol => Err(anyhow::Error::msg("Symbol values are not supported")),
                    ValueType::Function => Err(anyhow::Error::msg("Function values are not supported")),
                    ValueType::External => Err(anyhow::Error::msg("External values are not supported")),
                    ValueType::Unknown => Err(anyhow::Error::msg("Unknown values are not supported")),
                },
                Err(e) => Err(anyhow::Error::from(e)),
            },
        }
    }

    #[napi(
        ts_args_type = "value: YArray | YMap | YText | boolean | number | string | Record<string, any> | null | \
                        undefined"
    )]
    pub fn push(&mut self, value: MixedRefYType) -> Result<()> {
        self.insert(self.length(), value)
    }

    #[napi(
        ts_args_type = "value: YArray | YMap | YText | boolean | number | string | Record<string, any> | null | \
                        undefined"
    )]
    pub fn unshift(&mut self, value: MixedRefYType) -> Result<()> {
        self.insert(0, value)
    }

    #[napi]
    pub fn delete(&mut self, index: i64, len: Option<i64>) -> Result<()> {
        self.array
            .write()
            .unwrap()
            .remove(index as u64, len.unwrap_or(1) as u64)
            .map_err(anyhow::Error::from)
    }

    #[napi]
    pub fn iter(&self, env: Env) -> YArrayIterator {
        YArrayIterator {
            array: self.clone(),
            env,
            current: 0,
        }
    }

    #[napi]
    pub fn to_array(&self, env: Env) -> Result<JsArray> {
        let mut js_array = env.create_array(0)?;
        let array = self.array.read().unwrap();
        let doc = array.doc();
        for value in array.iter() {
            js_array.insert(get_js_unknown_from_value(env, doc, value)?)?;
        }
        Ok(js_array)
    }

    #[napi(js_name = "toJSON")]
    pub fn to_json(&self, env: Env) -> Result<JsArray> {
        let mut js_array = env.create_array(0)?;
        let array = self.array.read().unwrap();
        let doc = array.doc();
        for value in array.iter() {
            js_array.insert(get_js_unknown_from_value(env, doc, value)?)?;
        }
        Ok(js_array)
    }

    // TODO(@darkskygit): impl type based observe
    #[napi]
    pub fn observe(&mut self, _callback: JsFunction) -> Result<()> {
        Ok(())
    }

    // TODO(@darkskygit): impl type based observe
    #[napi]
    pub fn observe_deep(&mut self, _callback: JsFunction) -> Result<()> {
        Ok(())
    }
}

#[napi(iterator)]
pub struct YArrayIterator {
    array: YArray,
    env: Env,
    current: i64,
}

#[napi]
impl Generator for YArrayIterator {
    type Yield = MixedYType;

    type Next = Option<i64>;

    type Return = ();

    fn next(&mut self, value: Option<Self::Next>) -> Option<Self::Yield> {
        if self.array.length() <= self.current {
            return None;
        }
        let ret = self.array.get(self.env, self.current).ok();
        self.current = if let Some(value) = value.and_then(|v| v) {
            value
        } else {
            self.current + 1
        };
        ret
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_array_init() {
        let doc = YDoc::new(None);
        let array = doc.get_or_create_array("array".into()).unwrap();
        assert_eq!(array.length(), 0);
    }
}
