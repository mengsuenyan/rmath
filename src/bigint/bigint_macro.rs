
macro_rules! bigint_from_vec {
    ($Type0: ty) => {
        impl From<$Type0> for BigInt {
            fn from(x: $Type0) -> Self {
                Self {
                    nat: Nat::from(x),
                    sign: Natural,
                }
            }
        }
    };
    ($Type0: ty, $($Type1: ty),+) => {
        bigint_from_vec!($Type0);
        bigint_from_vec!($($Type1),+);
    }
}


macro_rules! bigint_from_basic {
    ($Type0: ty) => {
        impl From<$Type0> for BigInt {
            fn from(x: $Type0) -> Self {
                Self {
                    nat: Nat::from(x),
                    sign: BISign::Natural,
                }
            }
        }
    };
    ($Type0: ty, $($Type1: ty),+) => {
        bigint_from_basic!($Type0);
        bigint_from_basic!($($Type1),+);
    };
}

macro_rules! bigint_from_basici {
    (($Type0: ty, $TgtType0: ty)) => {
        impl From<$Type0> for BigInt {
            fn from(x: $Type0) -> Self {
                Self {
                    nat: Nat::from(x.abs() as $TgtType0),
                    sign: if x < 0 {BISign::Negative} else {BISign::Natural},
                }
            }
        }
    };
    (($Type0: ty, $TgtType0: ty), $(($Type1: ty, $TgtType1: ty)),+) => {
        bigint_from_basici!(($Type0, $TgtType0));
        bigint_from_basici!($(($Type1,$TgtType1)),+);
    };
}


macro_rules! bigint_ops_impl {
    (($Type0: ty, $TN0: ident, $TAN0: ident, $FN0: ident, $FAN0: ident, $IN: ident)) => {
        impl $TN0<$Type0> for BigInt {
            type Output = BigInt;
        
            fn $FN0(self, rhs: $Type0) -> Self::Output {
                let mut lhs = self.deep_clone();
                lhs.$IN(rhs);
                lhs
            }
        }
        
        impl $TAN0<$Type0> for BigInt {
            fn $FAN0(&mut self, rhs: $Type0) {
                self.$IN(rhs)
            }
        }
    };
    
    (($Type0: ty, $TN0: ident, $TAN0: ident, $FN0: ident, $FAN0: ident, $IN0: ident), $(($Type1: ty, $TN1: ident, $TAN1: ident, $FN1: ident, $FAN1: ident, $IN1: ident)),+) => {
        bigint_ops_impl!(($Type0, $TN0, $TAN0, $FN0, $FAN0, $IN0));
        bigint_ops_impl!($(($Type1, $TN1, $TAN1, $FN1, $FAN1, $IN1)),+);
    }
}

macro_rules! bigint_fmt_impl {
    (($TN0: ident, $FS0: literal, $FS1: literal)) => {
        impl $TN0 for BigInt {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                let nat = if f.alternate() {
                    format!($FS0, self.nat)
                } else {
                    format!($FS1, self.nat)
                };
                
                if self.is_negative() {
                    write!(f, "-{}", nat)
                } else {
                    write!(f, "{}", nat)
                }
            }
        }
    };
    (($TN0: ident, $FS0: literal, $FS01: literal), $(($TN1: ident, $FS1: literal, $FS11: literal)),+) => {
        bigint_fmt_impl!(($TN0, $FS0, $FS01));
        bigint_fmt_impl!($(($TN1, $FS1, $FS11)),+);
    };
}