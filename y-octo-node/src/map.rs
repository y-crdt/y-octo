use napi::{bindgen_prelude::Array as JsArray, iterator::Generator, Env, JsFunction, JsObject, JsUnknown, ValueType};
use y_octo::{Any, Map, Value};

use super::*;

#[napi]
#[derive(Clone)]
pub struct YMap {
    pub(crate) map: Map,
}

#[napi]
impl YMap {
    pub(crate) fn inner_new(map: Map) -> Self {
        Self { map }
    }

    #[napi(getter)]
    pub fn length(&self) -> i64 {
        self.map.len() as i64
    }

    #[napi(getter)]
    pub fn size(&self) -> i64 {
        self.length()
    }

    #[napi(getter)]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    #[napi(getter)]
    pub fn item_id(&self) -> Option<YId> {
        self.map.id().map(|id| YId { id })
    }

    #[napi(ts_generic_types = "T = unknown", ts_return_type = "T")]
    pub fn get(&self, env: Env, key: String) -> Result<MixedYType> {
        let value = if let Some(value) = self.map.get(&key) {
            get_mixed_y_type_from_value(env, value, false)?
        } else {
            MixedYType::D(env.get_undefined()?.into_unknown())
        };

        Ok(value)
    }

    #[napi(
        ts_generic_types = "T = YArray | YMap | YText | boolean | number | string | Record<string, any> | null | \
                            undefined",
        ts_args_type = "key: string, value: T",
        ts_return_type = "T"
    )]
    pub fn set(&mut self, env: Env, key: String, value: MixedRefYType) -> Result<MixedYType> {
        match value {
            MixedRefYType::A(array) => {
                self.map.insert(key, array.array.clone())?;
                Ok(array.into())
            }
            MixedRefYType::B(map) => {
                self.map.insert(key, map.map.clone())?;
                Ok(map.into())
            }
            MixedRefYType::C(text) => {
                self.map.insert(key, text.text.clone())?;
                Ok(text.into())
            }
            MixedRefYType::D(unknown) => match unknown.get_type() {
                Ok(value_type) => match value_type {
                    ValueType::Undefined => {
                        self.map.insert(key, Any::Undefined)?;
                        Ok(MixedYType::D(env.get_undefined().map(|v| v.into_unknown())?))
                    }
                    ValueType::Null => {
                        self.map.insert(key, Any::Null)?;
                        Ok(MixedYType::D(env.get_null().map(|v| v.into_unknown())?))
                    }
                    ValueType::Boolean => match unknown.coerce_to_bool().and_then(|v| v.get_value()) {
                        Ok(boolean) => {
                            self.map.insert(key, boolean)?;
                            Ok(MixedYType::D(env.get_boolean(boolean).map(|v| v.into_unknown())?))
                        }
                        Err(e) => Err(anyhow::Error::from(e).context("Failed to coerce value to boolean")),
                    },
                    ValueType::Number => match unknown.coerce_to_number().and_then(|v| v.get_double()) {
                        Ok(number) => {
                            self.map.insert(key, number)?;
                            Ok(MixedYType::D(env.create_double(number).map(|v| v.into_unknown())?))
                        }
                        Err(e) => Err(anyhow::Error::from(e).context("Failed to coerce value to number")),
                    },
                    ValueType::String => {
                        match unknown
                            .coerce_to_string()
                            .and_then(|v| v.into_utf8())
                            .and_then(|s| s.as_str().map(|s| s.to_string()))
                        {
                            Ok(string) => {
                                self.map.insert(key, string.clone())?;
                                Ok(MixedYType::D(env.create_string(&string).map(|v| v.into_unknown())?))
                            }
                            Err(e) => Err(anyhow::Error::from(e).context("Failed to coerce value to string")),
                        }
                    }
                    ValueType::Object => match unknown.coerce_to_object().and_then(get_any_from_js_object) {
                        Ok(any) => {
                            self.map.insert(key, Value::Any(any.clone()))?;
                            Ok(MixedYType::D(get_js_unknown_from_any(env, any)?.into()))
                        }
                        Err(e) => Err(anyhow::Error::from(e).context("Failed to coerce value to object")),
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

    #[napi]
    pub fn delete(&mut self, key: String) {
        self.map.remove(&key);
    }

    #[napi]
    pub fn clear(&mut self) {
        let keys = self.map.keys().map(ToOwned::to_owned).collect::<Vec<_>>();
        for key in keys {
            self.map.remove(&key);
        }
    }

    #[napi(
        js_name = "toJSON",
        ts_generic_types = "T = unknown",
        ts_return_type = "Record<string, T>"
    )]
    pub fn to_json(&self, env: Env) -> Result<JsObject> {
        let mut js_object = env.create_object()?;
        for (key, value) in self.map.iter() {
            js_object.set(key, get_mixed_y_type_from_value(env, value, true))?;
        }
        Ok(js_object)
    }

    #[napi]
    pub fn entries(&self, env: Env) -> YMapEntriesIterator {
        YMapEntriesIterator {
            entries: self.map.iter().map(|(k, v)| (k.to_owned(), v)).collect(),
            env,
            current: 0,
        }
    }

    #[napi]
    pub fn keys(&self) -> YMapKeyIterator {
        YMapKeyIterator {
            keys: self.map.keys().map(ToOwned::to_owned).collect(),
            current: 0,
        }
    }

    #[napi]
    pub fn values(&self, env: Env) -> YMapValuesIterator {
        YMapValuesIterator {
            entries: self.map.iter().map(|(_, v)| v).collect(),
            env,
            current: 0,
        }
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
pub struct YMapEntriesIterator {
    entries: Vec<(String, Value)>,
    env: Env,
    current: i64,
}

#[napi]
impl Generator for YMapEntriesIterator {
    type Yield = JsArray;

    type Next = Option<i64>;

    type Return = ();

    fn next(&mut self, value: Option<Self::Next>) -> Option<Self::Yield> {
        let current = self.current as usize;
        if self.entries.len() <= current {
            return None;
        }
        let ret = if let Some((string, value)) = self.entries.get(current) {
            let mut js_array = self.env.create_array(2).ok()?;
            js_array.set(0, string).ok()?;
            js_array
                .set(1, get_mixed_y_type_from_value(self.env, value.clone(), false).ok()?)
                .ok()?;
            Some(js_array)
        } else {
            None
        };
        self.current = if let Some(value) = value.and_then(|v| v) {
            value
        } else {
            self.current + 1
        };
        ret
    }
}

#[napi(iterator)]
pub struct YMapKeyIterator {
    keys: Vec<String>,
    current: i64,
}

#[napi]
impl Generator for YMapKeyIterator {
    type Yield = String;

    type Next = Option<i64>;

    type Return = ();

    fn next(&mut self, value: Option<Self::Next>) -> Option<Self::Yield> {
        let current = self.current as usize;
        if self.keys.len() <= current {
            return None;
        }
        let ret = self.keys.get(current).cloned();
        self.current = if let Some(value) = value.and_then(|v| v) {
            value
        } else {
            self.current + 1
        };
        ret
    }
}

#[napi(iterator)]
pub struct YMapValuesIterator {
    entries: Vec<Value>,
    env: Env,
    current: i64,
}

#[napi]
impl Generator for YMapValuesIterator {
    type Yield = MixedYType;

    type Next = Option<i64>;

    type Return = ();

    fn next(&mut self, value: Option<Self::Next>) -> Option<Self::Yield> {
        let current = self.current as usize;
        if self.entries.len() <= current {
            return None;
        }
        let ret = if let Some(value) = self.entries.get(current) {
            get_mixed_y_type_from_value(self.env, value.clone(), false).ok()
        } else {
            None
        };
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
    fn test_map_init() {
        let doc = YDoc::new(None);
        let text = doc.get_or_create_map("map".into()).unwrap();
        assert_eq!(text.length(), 0);
    }
}
