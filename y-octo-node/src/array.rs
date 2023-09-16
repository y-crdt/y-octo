use napi::{bindgen_prelude::Array as JsArray, Env, JsUnknown, ValueType};
use y_octo::{Any, Array};

use super::*;

#[napi]
pub struct YArray {
    pub(crate) array: Array,
}

#[napi]
impl YArray {
    pub(crate) fn new(array: Array) -> Self {
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

    #[napi]
    pub fn get(&self, env: Env, char_index: i64) -> Result<Option<JsUnknown>> {
        if let Some(value) = self.array.get(char_index as u64) {
            get_js_unknown_from_value(env, value)
                .map(Some)
                .map_err(|e| anyhow::Error::from(e))
        } else {
            Ok(None)
        }
    }

    #[napi]
    pub fn insert(&mut self, char_index: i64, value: JsUnknown) -> Result<()> {
        match value.get_type() {
            Ok(value_type) => match value_type {
                ValueType::Undefined | ValueType::Null => self
                    .array
                    .insert(char_index as u64, Any::Null)
                    .map_err(|e| anyhow::Error::from(e)),
                ValueType::Boolean => {
                    if let Ok(boolean) = value.coerce_to_bool().and_then(|v| v.get_value()) {
                        self.array
                            .insert(char_index as u64, boolean)
                            .map_err(|e| anyhow::Error::from(e))
                    } else {
                        Err(anyhow::Error::msg("Failed to coerce value to boolean"))
                    }
                }
                ValueType::Number => {
                    if let Ok(number) = value.coerce_to_number().and_then(|v| v.get_double()) {
                        self.array
                            .insert(char_index as u64, number)
                            .map_err(|e| anyhow::Error::from(e))
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
                        self.array
                            .insert(char_index as u64, string)
                            .map_err(|e| anyhow::Error::from(e))
                    } else {
                        Err(anyhow::Error::msg("Failed to coerce value to string"))
                    }
                }
                ValueType::Object => Err(anyhow::Error::msg("Object values are not supported yet")),
                ValueType::Symbol => Err(anyhow::Error::msg("Symbol values are not supported")),
                ValueType::Function => Err(anyhow::Error::msg("Function values are not supported")),
                ValueType::External => Err(anyhow::Error::msg("External values are not supported")),
                ValueType::Unknown => Err(anyhow::Error::msg("Unknown values are not supported")),
            },
            Err(e) => Err(anyhow::Error::from(e)),
        }
    }

    #[napi]
    pub fn remove(&mut self, char_index: i64, len: i64) -> Result<()> {
        self.array
            .remove(char_index as u64, len as u64)
            .map_err(|e| anyhow::Error::from(e))
    }

    #[napi]
    pub fn to_json(&self, env: Env) -> Result<JsArray> {
        let mut js_array = env.create_array(self.array.len() as u32)?;
        for value in self.array.iter() {
            js_array.insert(get_js_unknown_from_value(env, value)?)?;
        }
        Ok(js_array)
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_array_init() {
        let doc = Doc::new(None);
        let array = doc.get_or_create_array("array".into()).unwrap();
        assert_eq!(array.length(), 0);
    }
}
