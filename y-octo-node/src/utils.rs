use napi::{Env, JsUnknown, Result};
use y_octo::Any;

pub fn get_js_unknown_from_value(env: Env, any: Any) -> Result<JsUnknown> {
    match any {
        Any::Null | Any::Undefined => env.get_null().map(|v| v.into_unknown()),
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
                js_array.set_element(i as u32, get_js_unknown_from_value(env, value)?)?;
            }
            Ok(js_array.into_unknown())
        }
        _ => env.get_null().map(|v| v.into_unknown()),
    }
}
