
macro_rules! float_impl_from_basic {
    ($Fuc: ident, $Tgt: ty, $T: ty) => {
        impl From<$T> for Float {
            fn from(num: $T) -> Float {
                let mut f = Self::default();
                f.$Fuc(num as $Tgt);
                f
            }
        }
    };
    ($Fuc: ident, $Tgt: ty, $T0: ty, $($T1: ty),+) => {
        float_impl_from_basic!($Fuc, $Tgt, $T0);
        float_impl_from_basic!($Fuc, $Tgt, $($T1),+);
    }
}