use super::*;

pub type MixedRefYType<'a> = Either4<&'a YArray, &'a YMap, &'a YText, JsUnknown>;

pub type MixedYType = Either4<YArray, YMap, YText, JsUnknown>;

//make a macro to generate the impl Into<MixedYType> for each type

macro_rules! impl_into_mixed_y_type {
    ($type:ty, $enum:ident) => {
        impl Into<MixedYType> for $type {
            fn into(self) -> MixedYType {
                MixedYType::$enum(self.clone())
            }
        }
    };
}

impl_into_mixed_y_type!(YArray, A);
impl_into_mixed_y_type!(&YArray, A);
impl_into_mixed_y_type!(YMap, B);
impl_into_mixed_y_type!(&YMap, B);
impl_into_mixed_y_type!(YText, C);
impl_into_mixed_y_type!(&YText, C);
