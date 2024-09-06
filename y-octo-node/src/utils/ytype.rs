use super::*;
use napi::bindgen_prelude::ClassInstance;
use std::ops::Deref;

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

type MixedYTypeInstance = Either4<ClassInstance<YArray>, ClassInstance<YMap>, ClassInstance<YText>, JsUnknown>;

pub struct MixedYTypeClass(pub MixedYTypeInstance);

impl TryFrom<(Env, MixedYType)> for MixedYTypeClass {
    type Error = napi::Error;

    fn try_from(params: (Env, MixedYType)) -> Result<Self> {
        let (env, instance) = params;
        let ret = match instance {
            Either4::A(i) => MixedYTypeInstance::A(i.into_instance(env)?),
            Either4::B(i) => MixedYTypeInstance::B(i.into_instance(env)?),
            Either4::C(i) => MixedYTypeInstance::C(i.into_instance(env)?),
            Either4::D(i) => MixedYTypeInstance::D(i),
        };
        Ok(Self(ret))
    }
}

impl Deref for MixedYTypeClass {
    type Target = MixedYTypeInstance;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
