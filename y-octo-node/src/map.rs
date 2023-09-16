use napi::{bindgen_prelude::Object, Env, JsUnknown, ValueType};
use y_octo::{Any, Map, Value};

use super::*;

#[napi]
pub struct YMap {
    pub(crate) map: Map,
}

#[napi]
impl YMap {
    pub(crate) fn new(map: Map) -> Self {
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

    #[napi]
    pub fn get(&self, env: Env, key: String) -> Result<Option<JsUnknown>> {
        if let Some(value) = self.map.get(&key) {
            match value {
                Value::Any(any) => get_js_unknown_from_any(env, any),
                Value::Array(array) => env.create_external(YArray { array }, None).map(|o| o.into_unknown()),
                Value::Map(map) => env.create_external(YMap { map }, None).map(|o| o.into_unknown()),
                Value::Text(text) => env.create_external(YText { text }, None).map(|o| o.into_unknown()),
                _ => env.get_null().map(|v| v.into_unknown()),
            }
            .map(Some)
            .map_err(anyhow::Error::from)
        } else {
            Ok(None)
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
                    if let Ok(any) = get_any_from_js_unknown(value) {
                        self.map.insert(key, Value::Any(any)).map_err(anyhow::Error::from)
                    } else {
                        Err(anyhow::Error::msg("Failed to coerce value to array"))
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
    pub fn remove(&mut self, key: String) {
        self.map.remove(&key);
    }

    #[napi]
    pub fn to_json(&self, env: Env) -> Result<Object> {
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
