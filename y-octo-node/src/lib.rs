use anyhow::Result;
use napi_derive::napi;

mod doc;
mod text;

pub use doc::Doc;
pub use text::Text;
