use anyhow::Result;
use napi_derive::napi;

mod array;
mod awareness;
mod doc;
mod function;
mod map;
mod text;
mod types;
mod utils;

pub use array::*;
pub use awareness::*;
pub use doc::*;
pub use function::*;
pub use map::*;
pub use text::*;
pub use types::*;

use utils::{
    get_any_from_js_object, get_any_from_js_unknown, get_js_unknown_from_any, get_js_unknown_from_value, MixedRefYType,
    MixedYType,
};
