use crate::bigint::{Nat, NatError};
use std::str::FromStr;
use crate::parse_err::ParseErrKind::BeginWithIllegalChar;
use std::ops::{Add, AddAssign, SubAssign, Sub, ShrAssign, Shr, Shl, ShlAssign,
               Div, DivAssign, Mul, MulAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign,
               BitXor, BitXorAssign, Not, Rem, RemAssign, Neg};
use std::cmp::Ordering;

use BISign::{Natural, Negative};
use std::fmt::{Display, Formatter, Octal, Binary, LowerHex, UpperHex, Debug};

#[derive(Copy, Clone, PartialEq, Eq)]
pub(super) enum BISign {
    Negative,
    Natural,
}

impl Not for BISign {
    type Output = BISign;

    fn not(self) -> Self::Output {
        match self {
            Negative => Natural,
            Natural => Negative,
        }
    }
}

impl PartialOrd for BISign {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Natural, Negative) => Some(Ordering::Greater),
            (Negative, Natural) => Some(Ordering::Less),
            _ => Some(Ordering::Equal),
        }
    }
}

impl Ord for BISign {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// The type `BigInt` provides natural number operations like the Add, Sub, Mul, Div and so on.
/// 
/// # Examples
/// 
/// ```Rust
/// use rmath::bigint::Nat;
/// use std::str::FromStr;
/// 
/// let (a, b) = (BigInt::from(u32::MAX), BigInt::from(u32::MAX));
/// let sum = a.clone() + b.clone();
/// let mul = sum * a + b;
/// println!("(({}+{})*{}) + {} = {}", a, b, a, b, mul);
/// 
/// let a = BigInt::from_str("2938462938472983472983659726349017249287491026512746239764525612965293865296239471239874193284792387498274256129746192347").unwrap();
/// let b = BigInt::from_str("298472983472983471903246121093472394872319615612417471234712061").unwrap();
/// println!("{} * {} = {}", a.clone(), b.clone(), a*b );
/// ```
/// Note: The implementation of the `Clone` trait just only provide a shadow clone of the data that purpose 
/// is to share the ownership of the data, and the `deep_clone` method provide a real clone of the data.
/// 
/// # Panics
/// 
/// The panic will occurred when the divisor or modulus is 0 in the `/` or `%` operation;
#[derive(Clone)]
pub struct BigInt {
    nat: Nat,
    sign: BISign,
}

impl BigInt {
    pub fn deep_clone(&self) -> Self {
        Self {
            nat: self.nat.deep_clone(),
            sign: self.sign,
        }
    }
    
    pub fn is_negative(&self) -> bool {
        !self.is_nan() && self.sign == Negative
    }
    
    pub fn is_positive(&self) -> bool {
        !self.is_nan() && self.sign == Natural && self.nat != 0u32
    }
    
    pub fn is_natural(&self) -> bool {
        !self.is_nan() && self.sign == Natural
    }
    
    pub fn set_natural(&mut self) {
        if !self.is_nan() {
            self.sign = Natural; 
        }
    }
    
    pub fn set_negative(&mut self) {
        if !self.is_nan() && self.nat != 0u32 {
            self.sign = Negative;
        }
    }
    
    fn is_nan(&self) -> bool {
        self.nat.is_nan()
    }
    
    pub fn abs(&self) -> BigInt {
        let mut b = self.deep_clone();
        b.abs_inner();
        b
    }
    
    fn abs_inner(&mut self) {
        self.sign = Natural;
    }

    /// 除法定理: 对于任何整数a和任何正整数n, , 存在唯一整数q和r, 满足0<= r < n, 且self=d*n+r  
    /// 对于任何整数a和任何非零整数n, , 存在唯一整数q和r, 满足0<= r < abs(n), 且self=d*n+r  
    pub fn rem_euclid(&self, n: BigInt) -> BigInt {
        let mut b = self.deep_clone();
        b.rem_euclid_inner(n);
        b
    }
    
    fn rem_euclid_inner(&mut self, n: BigInt) {
        self.rem_inner(n.clone());
        
        if self.is_negative() {
            if n.is_negative() {
                self.sub_inner(n);
            } else {
                self.add_inner(n);
            }
        }
    }

    /// 对于任何整数a和任何非零整数n, , 存在唯一整数q和r, 满足0<= r < abs(n), 且self=d*n+r  
    pub fn div_euclid(&self, n: BigInt) -> BigInt {
        let mut b = self.deep_clone();
        b.div_euclid_inner(n);
        b
    }
    
    fn div_euclid_inner(&mut self, n: BigInt) {
        let m = self.clone() % n.clone();
        let is_pos =  n.is_positive();
        self.div_inner(n);
        
        if m.is_negative() {
            if is_pos {
                self.sub_inner(BigInt::from(1))
            } else {
                self.add_inner(BigInt::from(1))
            }
        }
    }
    
    fn nan() -> BigInt {
        Self {
            nat: Nat::nan(),
            sign: Natural,
        }
    }
    
    /// 求公约数, 返回(d, x, y), 其中:
    /// d = gcd(self, other); d = self * x + other * y;  
    /// 如果self和other为非自然数, 那么返回None, 否则返回Some((d, x, y));  
    /// 
    /// 特殊情况:  
    /// gcd(a, 0) = a;  
    /// gcd(0, 0) = 0;  
    pub fn gcd(&self, other: Self) -> (BigInt, BigInt, BigInt) {
        if self.is_nan() || other.is_nan() {
            (BigInt::nan(), BigInt::nan(), BigInt::nan())
        } else if (self == &0u32) && (other == 0u32) {
            (BigInt::from(0), BigInt::from(0), BigInt::from(0))
        } else if (self == &0u32) && (other != 0u32) {
            (other.abs(), BigInt::from(0), 
                if other.is_negative() {BigInt::from(-1)} else {BigInt::from(1)}
            )
        } else if (self != &0u32) && (other == 0u32) {
            (self.abs(), 
                if self.is_negative() {BigInt::from(-1)} else {BigInt::from(1)},
                BigInt::from(0)
            )
        } else {
            let (lhs, is_lhs_lz) = if self.is_negative() {
                (-self.clone(), true)
            } else {
                (self.deep_clone(), false)
            };
            let (rhs, is_rhs_lz) = if other.is_negative() {
                (-other.clone(), true)
            } else {
                (other.deep_clone(), false)
            };

            let (d, mut x, mut y) = BigInt::gcd_extend(lhs, rhs);
            (
                d,
                if is_lhs_lz {x.neg_inner(); x} else {x}, 
                if is_rhs_lz {y.neg_inner(); y} else {y}
            )
        }
    }
    
    fn gcd_extend(lhs: BigInt, rhs: BigInt) -> (BigInt, BigInt, BigInt) {
        if rhs == 0u32 {
            (lhs, BigInt::from(1), BigInt::from(0))
        } else {
            let rem = lhs.clone() % rhs.clone();
            let mut div = lhs / rhs.clone();
            let (d_p, mut x_p, y_p) = BigInt::gcd_extend(rhs, rem);
            div.mul_inner(y_p.clone());
            x_p.sub_inner(div);
            (d_p, y_p, x_p)
        }
    }

    /// <<算法导论>>  
    /// 定理31.23: 若有d=gcd(a, n), 假设对于某些整数x'和y', 有d=ax'+ny'. 如果d|b, 则方程
    /// ax=b(mod n)有一个解的值位x0, 则x0=x'(b/d) mod n;  
    /// 假设方程ax=b(mod n)有解(即d|b, d=gcd(a,n)), 且x0是该方程的任意一个解. 因此, 该方程对模
    /// n恰有d个不同的解, 分别为xi=x0+i(n/d), 这里i=0,1,...,d-1;  
    pub fn mod_inverse(&self, other: BigInt) -> BigInt {
        if self.is_nan() || other.is_nan() {
            BigInt::nan()
        } else {
            let n = if other.is_negative() {
                other.abs()
            } else {
                other.deep_clone()
            };
            
            let g = if self.is_negative() {
                self.rem_euclid(n.clone())
            } else {
                self.deep_clone()
            };
            
            // g*x + n*y = d
            let (_d, mut x, _y) = g.gcd(n.clone());
            if x.is_negative() {
                x.add_inner(n);
                x
            } else {
                x
            }
        }
    }
    
    fn add_inner(&mut self, rhs: Self) {
        match (self.sign, rhs.sign) {
            (Natural, Natural) => {
                self.nat += rhs.nat;
                self.sign = Natural;
            },
            (Negative, Negative) => {
                self.nat += rhs.nat;
                self.sign = Negative;
            },
            (Natural, Negative) => {
                self.sign = match self.nat.partial_cmp(&rhs.nat) {
                    None => Natural,
                    Some(Ordering::Greater) => Natural,
                    Some(Ordering::Less) => Negative,
                    Some(Ordering::Equal) => Natural,
                };
                self.nat -= rhs.nat;
            },
            (Negative, Natural) => {
                self.sign = match self.nat.partial_cmp(&rhs.nat) {
                    None => Natural,
                    Some(Ordering::Greater) =>  Negative,
                    Some(Ordering::Less) => Natural,
                    Some(Ordering::Equal) =>  Natural,
                };
                self.nat -= rhs.nat;
            }
        };
    }
    
    fn sub_inner(&mut self, rhs: Self) {
        match (self.sign, rhs.sign) {
            (Natural, Natural) => {
                self.sign = match self.nat.partial_cmp(&rhs.nat) {
                    None => Natural,
                    Some(Ordering::Less) => Negative,
                    Some(Ordering::Greater) => Natural,
                    Some(Ordering::Equal) => Natural,
                };
                self.nat -= rhs.nat;
            },
            (Negative, Negative) => {
                self.sign = match self.nat.partial_cmp(&rhs.nat) {
                    None => Natural,
                    Some(Ordering::Less) => Natural,
                    Some(Ordering::Greater) => Negative,
                    Some(Ordering::Equal) => Natural,
                };
                self.nat -= rhs.nat;
            },
            (Natural, Negative) => {
                self.sign = Natural;
                self.nat += rhs.nat;
            },
            (Negative, Natural) => {
                self.sign = Negative;
                self.nat += rhs.nat;
            },
        };
    }
    
    fn shr_inner(&mut self, rhs: usize) {
        self.nat >>= rhs;
        if self.nat == 0u32 {
            self.sign = Natural;
        }
    }
    
    fn shl_inner(&mut self, rhs: usize) {
        self.nat <<= rhs;
    }
    
    fn div_inner(&mut self, rhs: Self) {
        assert_ne!(rhs.nat, 0u32, "The divisor cannot be the 0");
        self.sign = match (self.sign, rhs.sign) {
            (Natural, Natural) => Natural,
            (Negative, Negative) => Natural,
            _ => match self.nat.partial_cmp(&0u32) {
                None => Natural,
                Some(Ordering::Equal) => Natural,
                _ => Negative,
            },
        };
        self.nat /= rhs.nat;
    }
    
    fn mul_inner(&mut self, rhs: Self) {
        self.sign = match (self.sign, rhs.sign) {
            (Natural, Natural) => Natural,
            (Negative, Negative) => Natural,
            _ => if self.nat.partial_cmp(&0u32) == Some(Ordering::Equal) ||
                    rhs.nat.partial_cmp(&0u32) == Some(Ordering::Equal) {
                Natural
            } else {
                Negative
            }
        };
        self.nat *= rhs.nat;
    }
    
    fn rem_inner(&mut self, rhs: Self) {
        assert_ne!(rhs.nat, 0u32, "the modulus can't be the 0");
        self.nat %= rhs.nat;
    }
    
    fn bitand_inner(&mut self, rhs: Self) {
        self.nat &= rhs.nat;
        self.sign = match self.nat.partial_cmp(&0u32) {
            None => Natural,
            Some(Ordering::Equal) => Natural,
            _ => match (self.sign, rhs.sign) {
                (Negative, Negative) => Negative,
                _ => Natural,
            }
        }
    }
    
    fn bitor_inner(&mut self, rhs: Self) {
        self.nat |= rhs.nat;
        self.sign = match self.nat.partial_cmp(&0u32) {
            None => Natural,
            Some(Ordering::Equal) => Natural,
            _ => match (self.sign, rhs.sign) {
                (Natural, Natural) => Natural,
                _ => Negative,
            }
        }
    }
    
    fn neg_inner(&mut self) {
        if !self.is_nan() {
            if *self != 0u32 {
                self.sign = !self.sign;
            }
        }
    }
    
    fn bitxor_inner(&mut self, rhs: Self) {
        self.nat ^= rhs.nat;
        self.sign = match self.nat.partial_cmp(&0u32) {
            None => Natural,
            Some(Ordering::Equal) => Natural,
            _ => match (self.sign, rhs.sign) {
                (Natural, Natural) => Natural,
                (Negative, Negative) => Natural,
                _ => Negative,
            }
        }
    }
}

bigint_from_basic!(u8, u16, u32, usize, u64, u128);
bigint_from_basici!((i8, u8), (i16, u16), (i32, u32), (isize, usize), (i64, u64), (i128, u128));
bigint_from_vec!(Vec<u8>, &Vec<u8>, &[u8], Vec<u32>, &Vec<u32>, &[u32], Nat);

impl FromStr for BigInt {
    type Err = NatError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();
        
        if s.is_empty() {
            Err(NatError::new(BeginWithIllegalChar, "empty string"))
        } else {
            let sign = if s.chars().next() == Some('-') {
                BISign::Negative
            } else {
                BISign::Natural
            };
            let nat = Nat::from_str(if sign == Negative {&s[1..]} else {s})?;
            Ok(
                Self {
                    nat,
                    sign,
                }
            )
        }
    }
}

impl Neg for BigInt {
    type Output = BigInt;

    fn neg(self) -> Self::Output {
        let mut b = self.deep_clone();
        b.neg_inner();
        b
    }
}

impl Not for BigInt {
    type Output = Self;

    fn not(self) -> Self::Output {
        let nat = !self.nat;
        let sign = match nat.partial_cmp(&0u32) {
            None => Natural,
            Some(Ordering::Equal) => Natural,
            _ => match self.sign {Natural => Negative, Negative => Natural,},
        };
        Self {
            nat,
            sign,
        }
    }
}

impl PartialEq for BigInt {
    fn eq(&self, other: &Self) -> bool {
        self.sign == other.sign && self.nat == other.nat
    }
}

impl PartialEq<u32> for BigInt {
    fn eq(&self, other: &u32) -> bool {
        self.sign == Natural && self.nat == *other
    }
}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.is_nan() || other.is_nan() {
            None
        } else {
            Some(self.sign.cmp(&other.sign).then_with(|| {
                let x = self.nat.partial_cmp(&other.nat).unwrap();
                if self.sign == Natural {
                    x
                } else {
                    x.reverse()
                }
            }))
        }
    }
}

bigint_ops_impl!(
    (BigInt, Add, AddAssign, add, add_assign, add_inner),
    (BigInt, BitAnd, BitAndAssign, bitand, bitand_assign, bitand_inner),
    (BigInt, BitOr, BitOrAssign, bitor, bitor_assign, bitor_inner),
    (BigInt, BitXor, BitXorAssign, bitxor, bitxor_assign, bitxor_inner),
    (usize, Shr, ShrAssign, shr, shr_assign, shr_inner),
    (usize, Shl, ShlAssign, shl, shl_assign, shl_inner),
    (BigInt, Sub, SubAssign, sub, sub_assign, sub_inner),
    (BigInt, Mul, MulAssign, mul, mul_assign, mul_inner),
    (BigInt, Div, DivAssign, div, div_assign, div_inner),
    (BigInt, Rem, RemAssign, rem, rem_assign, rem_inner)
);

bigint_fmt_impl!(
    (Display, "{}", "{}"),
    (Octal, "{:#o}", "{:o}"),
    (LowerHex, "{:#x}", "{:x}"),
    (UpperHex, "{:#X}", "{:X}"),
    (Debug, "{:#?}", "{:?}"),
    (Binary, "{:#b}", "{:#b}")
);

#[cfg(test)]
mod tests;