use napi::{Env, JsUnknown, ValueType};
use y_octo::{Any, Array, Value};

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
    pub fn len(&self) -> i64 {
        self.array.len() as i64
    }

    #[napi(getter)]
    pub fn is_empty(&self) -> bool {
        self.array.is_empty()
    }

    #[napi]
    pub fn get(&self, env: Env, char_index: i64) -> Result<Option<JsUnknown>> {
        if let Some(value) = self.array.get(char_index as u64) {
            match value {
                Value::Any(Any::Null | Any::Undefined) => env.get_null().map(|v| v.into_unknown()),
                Value::Any(Any::True) => env.get_boolean(true).map(|v| v.into_unknown()),
                Value::Any(Any::False) => env.get_boolean(false).map(|v| v.into_unknown()),
                Value::Any(Any::Integer(number)) => env.create_int32(number).map(|v| v.into_unknown()),
                Value::Any(Any::BigInt64(number)) => env.create_int64(number).map(|v| v.into_unknown()),
                Value::Any(Any::Float32(number)) => env.create_double(number.0 as f64).map(|v| v.into_unknown()),
                Value::Any(Any::Float64(number)) => env.create_double(number.0).map(|v| v.into_unknown()),
                Value::Any(Any::String(string)) => env.create_string(string.as_str()).map(|v| v.into_unknown()),
                // Value::Any(Any::Array(array)) => {
                //     let array = env.create_array_with_length(array.len() as u32)?;
                //     for (i, value) in array.iter().enumerate() {
                //         array.set_element(i as u32, value)?;
                //     }
                //     Ok(array.into_unknown())
                // }
                Value::Array(array) => env.create_external(YArray { array }, None).map(|o| o.into_unknown()),
                // Value::Map(map) => env.create_external(YMap { map }, None).map(|o| o.into_unknown()),
                Value::Text(text) => env.create_external(YText { text }, None).map(|o| o.into_unknown()),
                _ => env.get_null().map(|v| v.into_unknown()),
            }
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
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_array_init() {
        let doc = Doc::new(None);
        let text = doc.get_or_create_array("text".into()).unwrap();
        assert_eq!(text.len(), 0);
    }
}
