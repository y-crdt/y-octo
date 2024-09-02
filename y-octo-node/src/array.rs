use napi::{
    bindgen_prelude::{Array as JsArray, FromNapiValue},
    iterator::Generator,
    Env, JsFunction, JsUnknown, ValueType,
};
use y_octo::{Any, Array, Value};

use super::*;

#[napi]
#[derive(Clone)]
pub struct YArray {
    pub(crate) array: Array,
}

#[napi]
impl YArray {
    pub(crate) fn inner_new(array: Array) -> Self {
        Self { array }
    }

    #[napi(getter)]
    pub fn length(&self) -> i64 {
        self.array.len() as i64
    }

    #[napi(getter)]
    pub fn is_empty(&self) -> bool {
        self.array.is_empty()
    }

    #[napi(ts_generic_types = "T = unknown", ts_return_type = "T")]
    pub fn get(&self, env: Env, index: i64) -> Result<MixedYType> {
        if let Some(value) = self.array.get(index as u64) {
            match value {
                Value::Any(any) => get_js_unknown_from_any(env, any).map(MixedYType::D),
                Value::Array(array) => Ok(MixedYType::A(YArray::inner_new(array))),
                Value::Map(map) => Ok(MixedYType::B(YMap::inner_new(map))),
                Value::Text(text) => Ok(MixedYType::C(YText::inner_new(text))),
                _ => env.get_null().map(|v| v.into_unknown()).map(MixedYType::D),
            }
            .map_err(anyhow::Error::from)
        } else {
            Ok(MixedYType::D(env.get_null()?.into_unknown()))
        }
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
        for value in self.array.iter().skip(start as usize).take(end) {
            js_array.insert(get_js_unknown_from_value(env, value)?)?;
        }
        Ok(js_array)
    }

    #[napi(ts_generic_types = "T = unknown", ts_return_type = "Array<T>")]
    pub fn map(&self, env: Env, callback: JsFunction) -> Result<JsArray> {
        let mut js_array = env.create_array(0)?;
        for value in self.array.iter() {
            let js_value = get_js_unknown_from_value(env, value)?;
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
        match value {
            MixedRefYType::A(array) => self
                .array
                .insert(index as u64, array.array.clone())
                .map_err(anyhow::Error::from),
            MixedRefYType::B(map) => self
                .array
                .insert(index as u64, map.map.clone())
                .map_err(anyhow::Error::from),
            MixedRefYType::C(text) => self
                .array
                .insert(index as u64, text.text.clone())
                .map_err(anyhow::Error::from),
            MixedRefYType::D(unknown) => match unknown.get_type() {
                Ok(value_type) => match value_type {
                    ValueType::Undefined | ValueType::Null => {
                        self.array.insert(index as u64, Any::Null).map_err(anyhow::Error::from)
                    }
                    ValueType::Boolean => match unknown.coerce_to_bool().and_then(|v| v.get_value()) {
                        Ok(boolean) => self.array.insert(index as u64, boolean).map_err(anyhow::Error::from),
                        Err(e) => Err(anyhow::Error::new(e).context("Failed to coerce value to boolean")),
                    },
                    ValueType::Number => match unknown.coerce_to_number().and_then(|v| v.get_double()) {
                        Ok(number) => self.array.insert(index as u64, number).map_err(anyhow::Error::from),
                        Err(e) => Err(anyhow::Error::new(e).context("Failed to coerce value to number")),
                    },
                    ValueType::String => {
                        match unknown
                            .coerce_to_string()
                            .and_then(|v| v.into_utf8())
                            .and_then(|s| s.as_str().map(|s| s.to_string()))
                        {
                            Ok(string) => self.array.insert(index as u64, string).map_err(anyhow::Error::from),
                            Err(e) => Err(anyhow::Error::new(e).context("Failed to coerce value to string")),
                        }
                    }
                    ValueType::Object => match unknown
                        .coerce_to_object()
                        .and_then(|o| o.get_array_length().map(|l| (o, l)))
                    {
                        Ok((object, length)) => {
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

    #[napi(ts_generic_types = "T = unknown", ts_return_type = "Array<T>")]
    pub fn to_array(&self, env: Env) -> Result<JsArray> {
        let mut js_array = env.create_array(0)?;
        for value in self.array.iter() {
            js_array.insert(get_js_unknown_from_value(env, value)?)?;
        }
        Ok(js_array)
    }

    #[napi(js_name = "toJSON", ts_generic_types = "T = unknown", ts_return_type = "Array<T>")]
    pub fn to_json(&self, env: Env) -> Result<JsArray> {
        let mut js_array = env.create_array(0)?;
        for value in self.array.iter() {
            js_array.insert(get_js_unknown_from_value(env, value)?)?;
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
