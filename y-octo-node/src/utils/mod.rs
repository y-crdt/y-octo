mod ytype;

use super::*;
use napi::{bindgen_prelude::Either4, Env, Error, JsObject, JsUnknown, Result, Status, ValueType};
use y_octo::{AHashMap, Any, HashMapExt, Value};

pub use ytype::*;

pub fn get_js_unknown_from_any(env: Env, any: Any) -> Result<JsUnknown> {
    match any {
        Any::Undefined => env.get_undefined().map(|v| v.into_unknown()),
        Any::Null => env.get_null().map(|v| v.into_unknown()),
        Any::True => env.get_boolean(true).map(|v| v.into_unknown()),
        Any::False => env.get_boolean(false).map(|v| v.into_unknown()),
        Any::Integer(number) => env.create_int32(number).map(|v| v.into_unknown()),
        Any::BigInt64(number) => env.create_int64(number).map(|v| v.into_unknown()),
        Any::Float32(number) => env.create_double(number.0 as f64).map(|v| v.into_unknown()),
        Any::Float64(number) => env.create_double(number.0).map(|v| v.into_unknown()),
        Any::String(string) => env.create_string(string.as_str()).map(|v| v.into_unknown()),
        Any::Array(array) => {
            let mut js_array = env.create_array_with_length(array.len())?;
            for (i, value) in array.into_iter().enumerate() {
                js_array.set_element(i as u32, get_js_unknown_from_any(env, value)?)?;
            }
            Ok(js_array.into_unknown())
        }
        Any::Object(object) => {
            let mut js_object = env.create_object()?;
            for (key, value) in object.into_iter() {
                js_object.set_named_property(&key, get_js_unknown_from_any(env, value)?)?;
            }
            Ok(js_object.into_unknown())
        }
        _ => env.get_undefined().map(|v| v.into_unknown()),
    }
}

pub fn get_mixed_y_type_from_value(env: Env, value: Value, cascading: bool) -> Result<MixedYType> {
    match value {
        Value::Any(any) => get_js_unknown_from_any(env, any).map(MixedYType::D),
        Value::Array(array) => {
            if cascading {
                let mut js_array = env.create_array_with_length(array.len() as usize)?;
                for (i, value) in array.iter().enumerate() {
                    let value = get_mixed_y_type_from_value(env, value, cascading)?;
                    let instance = MixedClassYType::try_from((env, value))?;
                    js_array.set_element(i as u32, instance.into_inner())?;
                }
                Ok(MixedYType::D(js_array.into_unknown()))
            } else {
                Ok(YArray::inner_new(array).into())
            }
        }
        Value::Map(map) => {
            if cascading {
                let mut js_object = env.create_object()?;
                for (key, value) in map.iter() {
                    js_object.set_named_property(key, get_mixed_y_type_from_value(env, value, cascading)?)?;
                }
                Ok(MixedYType::D(js_object.into_unknown()))
            } else {
                Ok(YMap::inner_new(map).into())
            }
        }
        Value::Text(text) => Ok(YText::inner_new(text).into()),
        _ => env.get_undefined().map(|v| v.into_unknown()).map(MixedYType::D),
    }
}

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
