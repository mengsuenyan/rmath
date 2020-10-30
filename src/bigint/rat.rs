//! This file implements multi-precision rational numbers.

use crate::bigint::{BigInt, RatError, RatErrKind, Nat};
use crate::bigint::bigint::BISign::{Natural, Negative};
use crate::bigint::bigint::BISign;
use crate::bigint::util;
use std::ops::{Neg, Add, Sub, AddAssign, SubAssign, Mul, MulAssign, Div, DivAssign};
use std::cmp::Ordering;
use std::str::FromStr;
use std::fmt::{Debug, Formatter, Display, Binary, Octal, LowerHex, UpperHex};

/// A Rat represents a quotient a/b of arbitrary precision.  
/// The zero value for a Rat represents the value 0.  
///  
/// Operations always take pointer arguments (*Rat) rather  
/// than Rat values, and each unique Rat value requires  
/// its own unique *Rat pointer. To "copy" a Rat value,  
/// an existing (or newly allocated) Rat must be set to  
/// a new value using the Rat.Set method; shallow copies  
/// of Rats are not supported and may lead to errors.  
#[derive(Clone)]
pub struct Rat {
    // To make zero values for Rat work w/o initialization,
    // a zero value of b (len(b) == 0) acts like b == 1. At
    // the earliest opportunity (when an assignment to the Rat
    // is made), such uninitialized denominators are set to 1.
    // a.neg determines the sign of the Rat, b.neg is ignored.
    a: BigInt,
    b: BigInt,
}


impl Rat {
    pub fn is_nan(&self) -> bool {
        self.a.is_nan() || self.b.is_nan()
    }
    
    pub fn deep_clone(&self) -> Rat {
        Rat {
            a: self.a.deep_clone(),
            b: self.b.deep_clone(),
        }
    }
    
    pub fn from_frac(numerator: isize, denominator: isize) -> Result<Rat, RatError> {
        if denominator == 0 {
            Err(RatError::new(RatErrKind::DenominatorIsZero, ""))
        } else {
            let mut z = Rat {
                a: if denominator < 0 {BigInt::from(-numerator)} else {BigInt::from(numerator)},
                b: BigInt::from(denominator.abs()),
            };
            z.norm();
            Ok(z)
        }
    }
    
    pub fn from_frac_bigint(numerator: &BigInt, denominator: &BigInt) -> Result<Rat, RatError> {
        if denominator.nat == 0u32 {
            Err(RatError::new(RatErrKind::DenominatorIsZero, ""))
        } else {
            let mut z = Rat {
                a: if denominator.sign == Negative {BigInt::from(-numerator.clone())} else {BigInt::from(numerator.deep_clone())},
                b: BigInt::from(denominator.abs()),
            };
            z.norm();
            Ok(z)
        }
    }

    pub fn from_f64(f: f64) -> Rat {
        let exp_mask = (1<<11) - 1;
        let bits = f.to_bits();
        let mut mantissa = bits & ((1 << 52) - 1);
        let mut exp = ((bits >> 52) as i64) & exp_mask;
        
        if exp == exp_mask {
            // non-finite
            Rat {
                a: BigInt::nan(),
                b: BigInt::from(1u32),
            }
        } else {
            exp -= if exp == 0 {
                // denormal
                1022
            } else {
                // normal
                mantissa |= 1 << 52; 
                1023
            };
            
            let mut shift = 52 - exp;
            
            while (mantissa & 1) == 0 && shift > 0 {
                mantissa >>= 1;
                shift -= 1;
            }
            let mut a= BigInt::from(mantissa);
            a.sign = BISign::from(f < 0f64);
            let mut b = BigInt::from(1u32);
            let s = if shift > 0 {shift as usize} else {(-shift) as usize};
            b.nat.shl_inner(&s);
            
            let mut z = Rat {a, b};
            z.norm();
            z
        }
    }

    /// This method convert the `self` to the nearest `f32` value and a bool indicating
    /// whether the result represents `self` exactly. If the magnitude of `self` is too large to
    /// be represented by a `f32`, the result is an infinity and the bool is false.
    /// The sign of result always matches the sign of `self`, even if `self == 0`.
    pub fn to_f32(&self) -> (f32, bool) {
        let (f, exact) = if self.is_nan() {
            return (f32::NAN, false);
        } else if self.b.nat == 0u32 {
            Self::quo_to_f32(self.a.nat.clone(), Nat::from(1u32))
        } else {
            Self::quo_to_f32(self.a.nat.clone(), self.b.nat.clone())
        };
        
        if self.a.sign == Negative {
            (-f, exact)
        } else {
            (f, exact)
        }
    }

    /// This method convert the `self` to the nearest `f64` value and a bool indicating
    /// whether the result represents `self` exactly. If the magnitude of `self` is too large to
    /// be represented by a `f64`, the result is an infinity and the bool is false.
    /// The sign of result always matches the sign of `self`, even if `self == 0`.
    pub fn to_f64(&self) -> (f64, bool) {
        let (f, exact) = if self.is_nan() {
            return (f64::NAN, false);
        } else if self.b.nat == 0u32 {
            Self::quo_to_f64(self.a.nat.clone(), Nat::from(1u32))
        } else {
            Self::quo_to_f64(self.a.nat.clone(), self.b.nat.clone())
        };

        if self.a.sign == Negative {
            (-f, exact)
        } else {
            (f, exact)
        }
    }

    /// quotToFloat32 returns the non-negative float32 value  
    /// nearest to the quotient a/b, using round-to-even in  
    /// halfway cases. It does not mutate its arguments.  
    /// Preconditions: b is non-zero; a and b have no common factors.  
    fn quo_to_f32(a: Nat, b: Nat) -> (f32, bool) {
        debug_assert!(!a.is_nan() && !b.is_nan());
        debug_assert_ne!(b, 0u32);
        
        let (fsize, msize) = (32, 23);
        let (msize1, msize2) = (msize + 1, msize + 2);
        let esize = fsize - msize1;
        let ebias = (1 << (esize - 1)) - 1;
        let (emin, _emax) = (1 - ebias, ebias);
        
        if a == 0u32 {
            (0f32, true);
        }
        
        let (alen, blen) = (a.bits_len() as isize, b.bits_len() as isize);

        // 1. Left-shift A or B such that quotient A/B is in [1<<Msize1, 1<<(Msize2+1)
        // (Msize2 bits if A < B when they are left-aligned, Msize2+1 bits if A >= B).
        // This is 2 or 3 more than the float32 mantissa field width of Msize:
        // - the optional extra bit is shifted away in step 3 below.
        // - the high-order 1 is omitted in "normal" representation;
        // - the low-order 1 will be used during rounding then discarded.
        let mut exp = alen - blen;
        let (shift, is_great) = if msize2 > exp {((msize2 - exp) as usize, true)} else {((exp - msize2) as usize, false)};
        let (mut a2, mut b2) = (a.deep_clone(), b.deep_clone());
        if is_great {a2.shl_inner(&shift);} else {b2.shl_inner(&shift);}

        // 2. Compute quotient and remainder (q, r).  NB: due to the
        // extra shift, the low-order bit of q is logically the
        // high-order bit of r.
        // mantissa&1 && !haveRem => remainder is exactly half
        let (q, r) = (a2.clone() / b2.clone(), a2.clone() % b2.clone());
        let (mut mantissa, mut is_have_rem) = (q.as_vec()[0], r > 0u32); // mantissa&1 && !haveRem => remainder is exactly half

        // 3. If quotient didn't fit in Msize2 bits, redo division by b2<<1
        // (in effect---we accomplish this incrementally).
        if (mantissa >> msize2) == 1 {
            if mantissa & 1 == 1 {
                is_have_rem = true;
            }
            mantissa >>= 1;
            exp += 1;
        }
        
        if (mantissa >> msize1) != 1 {
            panic!("the numerator of {:#x} and the denominator of {:#x} have the common factor that great than 1", a, b);
        }
        
        // 4. Rounding.
        if (emin - msize) <= exp && exp <= emin {
            // Denormal case; lose 'shift' bits of precision.
            let shift = (emin - (exp - 1)) as usize; // [1..Esize1)
            let lostbits = mantissa & ((1 << shift) - 1);
            is_have_rem = is_have_rem || lostbits != 0;
            mantissa >>= shift;
            exp = 2 - ebias; // == exp + shift
        }
        
        // Round q using round-half-to-even.
        let mut exact = !is_have_rem;
        if (mantissa & 1) != 0 {
            exact = false;
            if is_have_rem || (mantissa & 2) != 0 {
                mantissa += 1;
                if mantissa >= (1 << msize2) {
                    // Complete rollover 11...1 => 100...0, so shift is safe
                    mantissa >>= 1;
                    exp += 1;
                }
            }
        }
        mantissa >>= 1; // discard rounding bit.  Mantissa now scaled by 1<<Msize1.

        let f = util::ldexp(mantissa as f64, exp - msize1) as f32;
        if f.is_infinite() {
            (f, false)
        } else {
            (f, exact)
        }
    }

    /// quotToFloat64 returns the non-negative float64 value
    /// nearest to the quotient a/b, using round-to-even in
    /// halfway cases. It does not mutate its arguments.
    /// Preconditions: b is non-zero; a and b have no common factors.    
    fn quo_to_f64(a: Nat, b: Nat) -> (f64, bool) {
        debug_assert!(!a.is_nan() && !b.is_nan());
        debug_assert_ne!(b, 0u32);
        let (fsize, msize) = (64, 52);
        let (msize1, msize2) = (msize + 1, msize + 2);
        let esize = fsize - msize1;
        let ebias = (1 << (esize - 1)) - 1;
        let (emin, _emax) = (1 - ebias, ebias);

        if a == 0u32 {
            return (0f64, true);
        }

        let (alen, blen) = (a.bits_len() as isize, b.bits_len() as isize);

        // 1. Left-shift A or B such that quotient A/B is in [1<<Msize1, 1<<(Msize2+1)
        // (Msize2 bits if A < B when they are left-aligned, Msize2+1 bits if A >= B).
        // This is 2 or 3 more than the float64 mantissa field width of Msize:
        // - the optional extra bit is shifted away in step 3 below.
        // - the high-order 1 is omitted in "normal" representation;
        // - the low-order 1 will be used during rounding then discarded.
        let mut exp = alen - blen;
        let (shift, is_great) = if msize2 > exp {((msize2 - exp) as usize, true)} else {((exp - msize2) as usize, false)};
        let (mut a2, mut b2) = (a.deep_clone(), b.deep_clone());
        if is_great {a2.shl_inner(&shift);} else {b2.shl_inner(&shift);}

        // 2. Compute quotient and remainder (q, r).  NB: due to the
        // extra shift, the low-order bit of q is logically the
        // high-order bit of r.
        let (q, r) = (a2.clone() / b2.clone(), a2.clone() % b2.clone());
        let (mut mantissa, mut is_have_rem) = if q.as_vec().len() > 1 {
                ((q.as_vec()[0] as u64) | ((q.as_vec()[1] as u64) << 32), r > 0u32)
            } else {
                (q.as_vec()[0] as u64, r > 0u32)
            }; // mantissa&1 && !haveRem => remainder is exactly half

        // 3. If quotient didn't fit in Msize2 bits, redo division by b2<<1
        // (in effect---we accomplish this incrementally).
        if (mantissa >> msize2) == 1 {
            if (mantissa & 1) == 1 {
                is_have_rem = true;
            }
            mantissa >>= 1;
            exp += 1;
        }

        if (mantissa >> msize1) != 1 {
            panic!("the numerator of {:#x} and the denominator of {:#x} have the common factor that great than 1", a, b);
        }

        // 4. Rounding.
        if (emin - msize) <= exp && exp <= emin {
            // Denormal case; lose 'shift' bits of precision.
            let shift = (emin - (exp - 1)) as usize; // [1..Esize1)
            let lostbits = mantissa & ((1 << shift) - 1);
            is_have_rem = is_have_rem || lostbits != 0;
            mantissa >>= shift;
            exp = 2 - ebias; // == exp + shift
        }
        
        // Round q using round-half-to-even.
        let mut exact = !is_have_rem;
        if (mantissa & 1) != 0 {
            exact = false;
            if is_have_rem || (mantissa & 2) != 0 {
                mantissa += 1;
                if mantissa >= (1 << msize2) {
                    // Complete rollover 11...1 => 100...0, so shift is safe
                    mantissa >>= 1;
                    exp += 1;
                }
            }
        }
        mantissa >>= 1; // discard rounding bit.  Mantissa now scaled by 1<<Msize1.

        let f = util::ldexp(mantissa as f64, exp - msize1);
        if f.is_infinite() {
            (f, false)
        } else {
            (f, exact)
        }
    }
    
    fn norm(&mut self) {
        let mut t = true;
        if self.a.is_nan() || self.a.nat == 0u32 {
            self.a.sign = Natural;
            t = false;
        }
        
        if self.b.is_nan() || self.b.nat == 0u32 {
            self.b.nat.clear();
            self.b.nat.as_mut_vec().push(1);
            t = false;
        }
        
        if t {
            let neg = self.a.sign;
            self.a.sign = Natural;
            self.b.sign = Natural;
            let (d, _x, _y) = self.a.gcd(self.b.clone());
            if d.nat != 1u32 {
                self.a.nat.div_inner(&d.nat);
                self.b.nat.div_inner(&d.nat);
            }
            
            self.a.sign = neg;
        }
    }
    
    pub fn abs(&self) -> Rat {
        let mut z = self.deep_clone();
        z.a.sign = Natural;
        z
    }
    
    pub(super) fn nan() -> Rat {
        Rat {
            a: BigInt::nan(),
            b: BigInt::from(1u32),
        }
    }
    
    pub fn inv(&self) -> Result<Rat, RatError> {
        if self.is_nan() {
            Ok(Self::nan())
        } else if self.a.nat == 0u32 {
            Err(RatError::new(RatErrKind::NumeratorIsZero, "It cannot to inverse zero"))
        } else {
            let (mut a, mut b) = (self.b.deep_clone(), self.a.deep_clone());
            a.sign = self.a.sign;
            b.sign = Natural;
            Ok(
                Rat {
                    a,
                    b,
                }
            )
        }
    }

    /// Sign returns:
    ///
    ///	Some(-1) if self <  0  
    ///	 Some(0) if self == 0  
    ///	Some(+1) if self >  0  
    /// None if self is not a number
    ///
    pub fn signnum(&self) -> Option<isize> {
        self.a.signnum()
    }
    
    /// whether is a integer number, `None` means `self` is not a number
    pub fn is_integer(&self) -> Option<bool> {
        if self.is_nan() {
            None
        } else {
            Some(self.a.nat == 0u32 || self.b == 1u32)
        }
    }
    
    pub fn numerator(&self) -> &BigInt {
        &self.a
    }
    
    pub fn denominator(&self) -> &BigInt {
        &self.b
    }
    
    fn clear(&mut self) {
        self.a.nat.clear();
    }
    
    fn mul_denom(x: &Nat, y: &Nat) -> Nat {
        if x == &0u32 && y == &0u32 {
            Nat::from(1u32)
        } else if x == &0u32 {
            y.deep_clone()
        } else if y == &0u32 {
            x.deep_clone()
        } else {
            x.clone() * y.clone()
        }
    }
    
    fn scale_denom(x: &BigInt, f: &Nat) -> BigInt {
        if f == &0u32 {
            x.deep_clone()
        } else {
            let n = x.nat.clone() * f.clone();
            let mut z = BigInt::from(n);
            z.sign = x.sign;
            z
        }
    }
    
    fn cmp_inner(&self, other: &Rat) -> Option<isize> {
        if self.is_nan() || other.is_nan() {None}
        else {
            let a = Self::scale_denom(&self.a, &other.b.nat);
            let b = Self::scale_denom(&other.a, &self.b.nat);
            Some(if a == b {0} else if a < b {-1} else {1})
        }
    }
    
    /// self and other must not be a Nan
    fn add_inner(&self, other: &Rat) -> Rat {
        let (mut a1, a2) = (
            Self::scale_denom(&self.a, &other.b.nat),
            Self::scale_denom(&other.a, &self.b.nat),
            );
        a1 += a2;
        let b = Self::mul_denom(&self.b.nat, &other.b.nat);
        let mut z = Rat {a: a1, b: BigInt {nat: b, sign: Natural}};
        z.norm();
        z
    }
    
    /// self and other must not be a Nan
    fn sub_inner(&self, other: &Rat) -> Rat {
        let (mut a1, a2) = (
            Self::scale_denom(&self.a, &other.b.nat),
            Self::scale_denom(&other.a, &self.b.nat),
            );
        a1 -= a2;
        
        let b = Self::mul_denom(&self.b.nat, &other.b.nat);
        let mut z = Rat {a: a1, b: BigInt {nat: b, sign: Natural}};
        z.norm();
        z
    }
    
    fn mul_inner(&self, other: &Rat) -> Rat {
        let mut z = if self == other {
            let a = self.a.sqr();
            let b = if self.b.nat == 0u32 {
                BigInt::from(1u32)
            } else {
                self.b.sqr()
            };
            Rat {
                a,
                b,
            }
        } else {
            let a = self.a.clone() * other.a.clone();
            let mut b = BigInt::from(Self::mul_denom(&self.b.nat, &other.b.nat));
            b.sign = Natural;
            Rat {
                a,
                b,
            }
        };
        
        z.norm();
        z
    }
    
    fn div_inner(&self, other: &Rat) -> Rat {
        if other.a.nat == 0u32 {
            panic!("division by zero");
        } else {
            let (mut a, b) = (
                Self::scale_denom(&self.a, &other.b.nat),
                Self::scale_denom(&other.a, &self.b.nat),
                );
            a.sign = BISign::from(a.sign != b.sign);
            let mut z = Rat {
                a,
                b,
            };
            z.norm();
            z
        }
    }
}

impl Div for Rat {
    type Output = Rat; 

    fn div(self, rhs: Self) -> Self::Output {
        if self.is_nan() || rhs.is_nan() {
            Rat::nan()
        } else {
            self.div_inner(&rhs)
        }
    }
}

impl DivAssign for Rat {
    fn div_assign(&mut self, rhs: Self) {
        if self.is_nan() || rhs.is_nan() {
            self.clear();
        } else {
            let z = self.div_inner(&rhs);
            *self = z;
        }
    }
}

impl Mul for Rat {
    type Output = Rat; 

    fn mul(self, rhs: Self) -> Self::Output {
        if self.is_nan() || rhs.is_nan() {
            Rat::nan()
        } else {
            self.mul_inner(&rhs)
        } 
    }
}

impl MulAssign for Rat {
    fn mul_assign(&mut self, rhs: Self) {
        if self.is_nan() {
            self.clear();
        } else {
            let z = self.mul_inner(&rhs);
            *self = z;
        }
    }
}

impl Sub for Rat {
    type Output = Rat; 

    fn sub(self, rhs: Self) -> Self::Output {
        if self.is_nan() || rhs.is_nan() {Rat::nan()}
        else {self.sub_inner(&rhs)}
    }
}

impl Add for Rat {
    type Output = Rat;

    fn add(self, rhs: Self) -> Self::Output {
        if self.is_nan() || rhs.is_nan() {Rat::nan()}
        else {self.add_inner(&rhs)}
    }
}

impl SubAssign for Rat {
    fn sub_assign(&mut self, rhs: Self) {
        if self.is_nan() || rhs.is_nan() {
            self.clear();
        } else {
            let z = self.sub_inner(&rhs);
            *self = z;
        }
    }
}

impl AddAssign for Rat {
    fn add_assign(&mut self, rhs: Self) {
        if self.is_nan() || rhs.is_nan() {
            self.clear();
        } else {
            let z = self.add_inner(&rhs);
            *self = z;
        }
    }
}

impl PartialEq for Rat {
    fn eq(&self, other: &Self) -> bool {
        match self.cmp_inner(other) {
            Some(0) => true,
            _ => false,
        }
    }
}

impl PartialOrd for Rat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.cmp_inner(other).map(|e| {
            if e == 0 {Ordering::Equal}
            else if e > 0 {Ordering::Greater}
            else {Ordering::Less}
        })
    }
}

impl Neg for Rat {
    type Output = Rat;

    fn neg(self) -> Self::Output {
        if self.is_nan() {
            Self::nan()
        } else {
            Rat {
                a: -self.a,
                b: self.b.deep_clone(),
            }
        }
    }
}

impl From<f64> for Rat {
    fn from(f: f64) -> Self {
        Self::from_f64(f)
    }
}

impl From<f32> for Rat {
    fn from(f: f32) -> Self {
        Self::from_f64(f as f64)
    }
}

macro_rules! rat_impl_from_basic {
    ($T: ty) => {
        impl From<$T> for Rat {
            fn from(n: $T) -> Self {
                Rat {
                    a: BigInt::from(n),
                    b: BigInt::from(1u32),
                }
            }
        }
    };
    ($T0: ty, $($T1: ty),+) => {
        rat_impl_from_basic!($T0);
        rat_impl_from_basic!($($T1),+);
    }
}

rat_impl_from_basic!(u8, u16, u32, usize, u64, u128, i8, i16, i32, isize, i64, i128, Nat);

impl From<BigInt> for Rat {
    fn from(n: BigInt) -> Self {
        Rat {
            a: n.deep_clone(),
            b: BigInt::from(1u32),
        }
    }
}

impl FromStr for Rat {
    type Err = RatError;

    /// parse string like "323290.0392038920", "-235252532/9403503402385403", "0b1000111/0b111111" or "0x3290523/0xab32342", and so on
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();
        
        if s.is_empty() {
            Err(RatError::new(RatErrKind::ParseStringWrong, "empty string"))
        } else if s.find('.').is_some() {
            match f64::from_str(s) {
                Ok(f) => {
                    if f.is_nan() {
                        Err(RatError::new(RatErrKind::ParseStringWrong, format!("{} is not a number", s)))
                    } else {
                        Ok(Rat::from(f))
                    }
                },
                Err(e) => {
                    Err(RatError::new(RatErrKind::ParseStringWrong, e))
                }
            }
        } else {
            let slash_idx = s.find('/');
            let (a, b) = match slash_idx {
                Some(i) => {
                    (BigInt::from_str(&s[..i]), BigInt::from_str(&s[(i+1)..]))
                },
                None => {
                    (BigInt::from_str(s), Ok(BigInt::from(1u32)))
                },
            };
            
            let mut a = match a {
                Ok(i) => i,
                Err(e) => { return Err(RatError::new(RatErrKind::ParseStringWrong, e)); }
            };
            let mut b = match b {
                Ok(i) => i,
                Err(e) => { return Err(RatError::new(RatErrKind::ParseStringWrong, e)); }
            };
            
            if a.is_nan() || b.is_nan() {
                Err(RatError::new(RatErrKind::ParseStringWrong, format!("`{}` is not a number", s)))
            } else if b.nat == 0u32 {
                Err(RatError::new(RatErrKind::DenominatorIsZero, ""))
            } else {
                a.sign = BISign::from(a.sign != b.sign);
                b.sign = Natural;
                Ok(Rat {a, b})
            }
        }
    }
}

macro_rules! impl_rat_fmt_inner {
    (($TraitName: ident, $FmtStr0: literal, $FmtStr1: literal)) => {
        impl $TraitName for Rat {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                if self.is_nan() {
                    write!(f, "{}", "NaN")
                } else {
                    let (mut a, b) = if f.alternate() {
                        (format!($FmtStr1, self.a),
                        format!($FmtStr1, self.b))
                    } else {
                        (format!($FmtStr0, self.a),
                        format!($FmtStr0, self.b))
                    };
                    a.push('/');
                    a.push_str(b.as_str());
                    write!(f, "{}", a)
                }
            }
        }
    };
    
    (($TraitName0: ident, $FmtStr00: literal, $FmtStr01: literal), $(($TraitName1: ident, $FmtStr10: literal, $FmtStr11: literal)),+) => {
        impl_rat_fmt_inner!(($TraitName0, $FmtStr00, $FmtStr01));
        impl_rat_fmt_inner!($(($TraitName1, $FmtStr10, $FmtStr11)),+);
    }
}

impl_rat_fmt_inner!(
    (Debug, "{:?}", "{:?}"),
    (Display, "{}", "{}"),
    (Binary, "{:b}", "{:#b}"),
    (Octal, "{:o}", "{:#o}"),
    (LowerHex, "{:x}", "{:#x}"),
    (UpperHex, "{:X}", "{:#X}")
    );

#[cfg(test)]
mod test;