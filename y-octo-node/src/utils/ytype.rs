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

pub struct MixedClassYType(pub JsUnknown);

impl TryFrom<(Env, MixedYType)> for MixedClassYType {
    type Error = napi::Error;

    fn try_from(params: (Env, MixedYType)) -> Result<Self> {
        let (env, instance) = params;
        let ret = match instance {
            Either4::A(i) => Either4::A(i.into_instance(env)?),
            Either4::B(i) => Either4::B(i.into_instance(env)?),
            Either4::C(i) => Either4::C(i.into_instance(env)?),
            Either4::D(i) => Either4::D(i),
        };
        Ok(Self(ret.as_unknown(env)))
    }
}

impl MixedClassYType {
    pub fn into_inner(self) -> JsUnknown {
        self.0
    }
}
