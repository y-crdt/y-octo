use napi::{Error, JsObject, Status, ValueType};
use y_octo::{AHashMap, Any, HashMapExt};

use super::*;

pub fn get_any_from_js_object(object: JsObject) -> Result<Any> {
    if let Ok(length) = object.get_array_length() {
        let mut array = Vec::with_capacity(length as usize);
        for i in 0..length {
            if let Ok(value) = object.get_element::<JsUnknown>(i) {
                array.push(get_any_from_js_unknown(value)?);
            }
        }
        Ok(Any::Array(array))
    } else {
        let mut map = AHashMap::new();
        let keys = object.get_property_names()?;
        if let Ok(length) = keys.get_array_length() {
            for i in 0..length {
                if let Ok((obj, key)) = keys.get_element::<JsUnknown>(i).and_then(|o| {
                    o.coerce_to_string()
                        .and_then(|obj| obj.into_utf8().and_then(|s| s.as_str().map(|s| (obj, s.to_string()))))
                }) {
                    if let Ok(value) = object.get_property::<_, JsUnknown>(obj) {
                        map.insert(key, get_any_from_js_unknown(value)?);
                    }
                }
            }
        }
        Ok(Any::Object(map))
    }
}

pub fn get_any_from_js_unknown(js_unknown: JsUnknown) -> Result<Any> {
    match js_unknown.get_type()? {
        ValueType::Undefined => Ok(Any::Undefined),
        ValueType::Null => Ok(Any::Null),
        ValueType::Boolean => Ok(js_unknown.coerce_to_bool().and_then(|v| v.get_value())?.into()),
        ValueType::Number => Ok(js_unknown
            .coerce_to_number()
            .and_then(|v| v.get_double())
            .map(|v| v.into())?),
        ValueType::String => Ok(js_unknown
            .coerce_to_string()
            .and_then(|v| v.into_utf8())
            .and_then(|s| s.as_str().map(|s| s.to_string()))?
            .into()),
        ValueType::Object => {
            if let Ok(object) = js_unknown.coerce_to_object() {
                get_any_from_js_object(object)
            } else {
                Err(Error::new(Status::InvalidArg, "Failed to coerce value to object"))
            }
        }
        _ => Err(Error::new(Status::InvalidArg, "Failed to coerce value to any")),
    }
}
