use napi::{bindgen_prelude::Either4, Env, JsObject, JsUnknown, ValueType};
use y_octo::{Any, Map, Value};

use super::*;

#[napi]
pub struct YMap {
    pub(crate) map: Map,
}

#[napi]
impl YMap {
    #[napi(constructor)]
    pub fn new() -> Self {
        unimplemented!()
    }

    pub(crate) fn inner_new(map: Map) -> Self {
        Self { map }
    }

    #[napi(getter)]
    pub fn length(&self) -> i64 {
        self.map.len() as i64
    }

    #[napi(getter)]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    #[napi(ts_generic_types = "T = unknown", ts_return_type = "T")]
    pub fn get(&self, env: Env, key: String) -> Result<MixedYType> {
        if let Some(value) = self.map.get(&key) {
            match value {
                Value::Any(any) => get_js_unknown_from_any(env, any).map(Either4::D),
                Value::Array(array) => Ok(Either4::A(YArray::inner_new(array))),
                Value::Map(map) => Ok(Either4::B(YMap::inner_new(map))),
                Value::Text(text) => Ok(Either4::C(YText::inner_new(text))),
                _ => env.get_null().map(|v| v.into_unknown()).map(Either4::D),
            }
            .map_err(anyhow::Error::from)
        } else {
            Ok(Either4::D(env.get_null()?.into_unknown()))
        }
    }

    #[napi]
    pub fn set(&mut self, key: String, value: JsUnknown) -> Result<()> {
        match value.get_type() {
            Ok(value_type) => match value_type {
                ValueType::Undefined | ValueType::Null => self.map.insert(key, Any::Null).map_err(anyhow::Error::from),
                ValueType::Boolean => {
                    if let Ok(boolean) = value.coerce_to_bool().and_then(|v| v.get_value()) {
                        self.map.insert(key, boolean).map_err(anyhow::Error::from)
                    } else {
                        Err(anyhow::Error::msg("Failed to coerce value to boolean"))
                    }
                }
                ValueType::Number => {
                    if let Ok(number) = value.coerce_to_number().and_then(|v| v.get_double()) {
                        self.map.insert(key, number).map_err(anyhow::Error::from)
                    } else {
                        Err(anyhow::Error::msg("Failed to coerce value to number"))
                    }
                }
                ValueType::String => {
                    if let Ok(string) = value
                        .coerce_to_string()
                        .and_then(|v| v.into_utf8())
                        .and_then(|s| s.as_str().map(|s| s.to_string()))
                    {
                        self.map.insert(key, string).map_err(anyhow::Error::from)
                    } else {
                        Err(anyhow::Error::msg("Failed to coerce value to string"))
                    }
                }
                ValueType::Object => {
                    if let Ok(object) = value.coerce_to_object() {
                        let any = get_any_from_js_object(object)?;
                        self.map.insert(key, Value::Any(any)).map_err(anyhow::Error::from)
                    } else {
                        Err(anyhow::Error::msg("Failed to coerce object to array"))
                    }
                }
                ValueType::Symbol => Err(anyhow::Error::msg("Symbol values are not supported")),
                ValueType::Function => Err(anyhow::Error::msg("Function values are not supported")),
                ValueType::External => Err(anyhow::Error::msg("External values are not supported")),
                ValueType::Unknown => Err(anyhow::Error::msg("Unknown values are not supported")),
            },
            Err(e) => Err(anyhow::Error::from(e)),
        }
    }

    #[napi]
    pub fn set_array(&mut self, key: String, array: &YArray) -> Result<()> {
        self.map.insert(key, Value::Array(array.array.clone()))?;

        Ok(())
    }

    #[napi]
    pub fn set_map(&mut self, key: String, map: &YMap) -> Result<()> {
        self.map.insert(key, Value::Map(map.map.clone()))?;

        Ok(())
    }

    #[napi]
    pub fn set_text(&mut self, key: String, text: &YText) -> Result<()> {
        self.map.insert(key, Value::Text(text.text.clone()))?;

        Ok(())
    }

    #[napi]
    pub fn remove(&mut self, key: String) {
        self.map.remove(&key);
    }

    #[napi]
    pub fn to_json(&self, env: Env) -> Result<JsObject> {
        let mut js_object = env.create_object()?;
        for (key, value) in self.map.iter() {
            js_object.set(key, get_js_unknown_from_value(env, value))?;
        }
        Ok(js_object)
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_map_init() {
        let doc = Doc::new(None);
        let text = doc.get_or_create_map("map".into()).unwrap();
        assert_eq!(text.length(), 0);
    }
}
