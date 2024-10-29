use y_octo::{Any, Value};

use super::*;

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
