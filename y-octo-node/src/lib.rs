use anyhow::Result;
use napi_derive::napi;

mod array;
mod doc;
mod function;
mod map;
mod text;
mod utils;

pub use array::YArray;
pub use doc::YDoc;
pub use function::{apply_update, encode_state_as_update, merge_updates};
pub use map::YMap;
pub use text::YText;

use utils::{
    get_any_from_js_object, get_any_from_js_unknown, get_js_unknown_from_any, get_js_unknown_from_value, MixedRefYType,
    MixedYType,
};
