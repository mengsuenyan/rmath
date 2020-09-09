
#[macro_export]
macro_rules! nat_from_basic {
    ($type: ty) => {
        impl From<$type> for Nat {
            fn from(x: $type) -> Self {
                if std::mem::size_of::<$type>() <= std::mem::size_of::<u32>() {
                    Nat {nat: Rc::new(Cell::new(vec![x as u32]))}
                } else {
                    let (mut v, mut arr) = (Vec::new(), [0;4]);
                    const MASK: usize = 3;
                    for (i, &ele) in x.to_le_bytes().iter().enumerate() {
                        if (MASK & i) == 0 && i > 3 {
                            v.push(u32::from_le_bytes(arr));
                        }
                        arr[MASK & i] = ele;
                    }
                    v.push(u32::from_le_bytes(arr));
                    Nat {nat: Rc::new(Cell::new(v))}
                }
            }
        }
    };
    
    ($type0: ty, $($type1: ty),+) => {
        nat_from_basic!($type0);
        nat_from_basic!($($type1),+);
    }
}

macro_rules! nat_fmt {
    (($trait_name: ident, $fmt_str: literal)) => {
        impl $trait_name for Nat {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                if self.is_nan() {
                    return write!(f, "{}", "NaN");
                }
                
                let mut nat: Vec<String> = self.as_vec().iter().rev().map(|&x| {format!($fmt_str, x)}).collect();
                match nat.first_mut() {
                    Some(x) => {
                        let mut y = String::with_capacity(x.len());
                        y.push_str(x.trim_start_matches('0'));
                        x.clear();
                        x.push_str(y.as_str());
                    }
                    None => {},
                }
                write!(f, "{}", nat.join(""))
            }
        }
    };
    
    (($trait_name0: ident, $fmt_str0: literal), $(($trait_name1: ident, $fmt_str1: literal)),+) => {
        nat_fmt!(($trait_name0, $fmt_str0));
        nat_fmt!($(($trait_name1, $fmt_str1)),+);
    }
}

macro_rules! nat_eq_basic {
    ($type0: ty) => {
        impl PartialEq<$type0> for Nat {
            fn eq(&self, other: &$type0) -> bool {
                if self.is_nan() {false}
                else {
                    let x = Nat::from(*other);
                    self.as_vec() == x.as_vec()
                }
            }
        }
    };
    ($type0: ty, $($type1: ty),+) => {
        nat_eq_basic!($type0);
        nat_eq_basic!($($type1),+);
    }
}

macro_rules! nat_ord_basic {
    ($type0: ty) => {
        impl PartialOrd<$type0> for Nat {
            fn partial_cmp(&self, other: &$type0) -> Option<Ordering> {
                let x = Nat::from(*other);
                self.partial_cmp(&x)
            }
        }
    };
    ($type0: ty, $($type1: ty),+) => {
        nat_ord_basic!($type0);
        nat_ord_basic!($($type1),+);
    }
}

macro_rules! nat_arith_ops {
    (($Rhs: ty, $trait_name: ident, $trait_assign_name: ident, $fn_name: ident, $fn_assign_name: ident, $fn_inner_name: ident, $rhs_is_nan: expr)) => {
        impl $trait_name<$Rhs> for Nat {
            type Output = Nat;
            fn $fn_name(self, rhs: $Rhs) -> Self::Output {
                if self.is_nan() || $rhs_is_nan(&rhs) {
                    Self::default()
                } else {
                    Nat::from(self.$fn_inner_name(&rhs))
                }
            }
        }
        
        impl $trait_assign_name<$Rhs> for Nat {
            fn $fn_assign_name(&mut self, rhs: $Rhs) {
                if self.is_nan() || $rhs_is_nan(&rhs) {
                    self.clear();
                } else {
                   let x = self.$fn_inner_name(&rhs);
                   self.clear();
                   self.as_mut_vec().extend_from_slice(x.as_slice());
                }
            }
        }
    };
    
    (($Rhs: ty, $trait_name: ident, $trait_assign_name: ident, $fn_name: ident, $fn_assign_name: ident, $fn_inner_name: ident, $rhs_is_nan: expr),
        $(($Rhs1: ty, $trait_name1: ident, $trait_assign_name1: ident, $fn_name1: ident, $fn_assign_name1: ident, $fn_inner_name1: ident, $rhs_is_nan1: expr)),+) => {
        nat_arith_ops!(($Rhs, $trait_name, $trait_assign_name, $fn_name, $fn_assign_name, $fn_inner_name, $rhs_is_nan));
        nat_arith_ops!($(($Rhs1, $trait_name1, $trait_assign_name1, $fn_name1, $fn_assign_name1, $fn_inner_name1, $rhs_is_nan1)),+);
    }
}