//! The implementation of Float convert from the Golang.
//! 
//! This file implements multi-precision floating-point numbers.  
//! Like in the GNU MPFR library (https://www.mpfr.org/), operands  
//! can be of mixed precision. Unlike MPFR, the rounding mode is  
//! not specified with each operation, but with each operand. The  
//! rounding mode of the result operand determines the rounding  
//! mode of an operation. This is a from-scratch implementation.  

pub use crate::bigint::float_para::{RoundingMode, Accuracy};
use crate::bigint::bigint::BISign;
use crate::bigint::{Nat, BigInt, Rat};
use crate::bigint::float_para::Form;
use crate::bigint::float_para::RoundingMode::{*};
use crate::bigint::bigint::BISign::{Negative, Natural};
use crate::bigint::arith::{add_vw_inner, shr_vu_inner};
use crate::bigint::arith_generic::shl_vu_inner;
use crate::bigint::util;
use std::ops::{Neg, Div, DivAssign, Add, AddAssign, Sub, SubAssign, Mul, MulAssign};
use std::cmp::Ordering;

/// A nonzero finite Float represents a multi-precision floating point number
///
///   sign × mantissa × 2**exponent
///
/// with 0.5 <= mantissa < 1.0, and MinExp <= exponent <= MaxExp.  
/// A Float may also be zero (+0, -0) or infinite (+Inf, -Inf).  
/// All Floats are ordered, and the ordering of two Floats x and y  
/// is defined by x.Cmp(y).
///
/// Each Float value also has a precision, rounding mode, and accuracy.  
/// The precision is the maximum number of mantissa bits available to  
/// represent the value. The rounding mode specifies how a result should  
/// be rounded to fit into the mantissa bits, and accuracy describes the  
/// rounding error with respect to the exact result.  
///
/// Unless specified otherwise, all operations (including setters) that  
/// specify a *Float variable for the result (usually via the receiver  
/// with the exception of mant_exp), round the numeric result according  
/// to the precision and rounding mode of the result variable.  
///
/// If the provided result precision is 0 (see below), it is set to the  
/// precision of the argument with the largest precision value before any  
/// rounding takes place, and the rounding mode remains unchanged. Thus,  
/// uninitialized Floats provided as result arguments will have their  
/// precision set to a reasonable value determined by the operands, and  
/// their mode is the zero value for RoundingMode (ToNearestEven).  
///
/// By setting the desired precision to 24 or 53 and using matching rounding  
/// mode (typically ToNearestEven), Float operations produce the same results  
/// as the corresponding float32 or float64 IEEE-754 arithmetic for operands  
/// that correspond to normal (i.e., not denormal) float32 or float64 numbers.  
/// Exponent underflow and overflow lead to a 0 or an Infinity for different  
/// values than IEEE-754 because Float exponents have a much larger range.  
///
/// The zero (uninitialized) value for a Float is ready to use and represents  
/// the number +0.0 exactly, with precision 0 and rounding mode ToNearestEven.  
///
/// Operations always take pointer arguments (*Float) rather  
/// than Float values, and each unique Float value requires  
/// its own unique *Float pointer. To "copy" a Float value,  
/// an existing (or newly allocated) Float must be set to  
/// a new value using the Float.Set method; shallow copies  
/// of Floats are not supported and may lead to errors.  
#[derive(Clone)]
pub struct Float {
    pub(super) mode: RoundingMode,
    pub(super) acc: Accuracy,
    pub(super) form: Form,
    pub(super) neg: BISign,
    pub(super) prec: usize,
    pub(super) exp: isize,
    pub(super) mant: Nat,
}

impl Float {
    pub fn deep_clone(&self) -> Float {
        Float {
            mode: self.mode,
            acc: self.acc,
            form: self.form,
            neg: self.neg,
            prec: self.prec,
            exp: self.exp,
            mant: self.mant.deep_clone(),
        }
    }
    
    pub fn is_nan(&self) -> bool {
        self.form.is_nan()
    }
    
    /// largest supported exponent
    pub const fn max_exp() -> isize {
        std::i32::MAX as isize
    }
    
    /// smallest supported exponent
    pub const fn min_exp() -> isize {
        std::i32::MIN as isize
    }
    
    /// largest (theoretically) supported precision
    pub const fn max_precision() -> usize {
        std::u32::MAX as usize
    }
    
    pub fn set_precision(&mut self, prec: usize) {
        self.acc = Accuracy::Exact;
        if prec == 0 {
            self.prec = 0;
            if self.form.is_finite() {
                self.acc = Self::make_accuracy(self.neg == Negative);
                self.form = Form::Zero;
            }
            return;
        }
        
        let prec = std::cmp::min(Self::max_precision(), prec);
        let old = self.prec;
        self.prec = prec;
        if self.prec < old {
            self.round(0)
        }
    }
    
    /// set the mode of `self` to `mode`, and convert the accuracy of `self` to the `Exact`
    pub fn set_mode(&mut self, mode: RoundingMode) {
        self.mode = mode;
        self.acc = Accuracy::Exact;
    }
    
    /// The result may be 0 for |x| == 0 and |x| == Inf.
    pub fn get_precision(&self) -> usize {
        self.prec
    }
    
    pub fn required_min_precision(&self) -> usize {
        if !self.form.is_finite() {
            0
        } else {
            (self.mant.as_vec().len() << 5) - self.mant.trailling_zeros()
        }
    }
    
    pub fn get_mode(&self) -> RoundingMode {
        self.mode
    }
    
    pub fn get_accuracy(&self) -> Accuracy {
        self.acc
    }

    ///	-1 if x <   0  
    ///	 0 if x is ±0  
    ///	+1 if x >   0  
    pub fn signnum(&self) -> Option<isize> {
        if self.is_nan() {
            None
        } else {
            Some(
                if self.form.is_zero() {
                    0
                } else if self.neg == Negative {
                    -1
                } else {
                    1
                }
            )
        }
    }
    
    pub fn get_inf(is_negative: bool) -> Float {
        let mut z = Self::default();
        z.form = Form::Inf;
        z.neg = BISign::from(is_negative);
        z
    }

    /// mant_exp breaks `self` into its mantissa and exponent components  
    /// and returns the exponent. If a non-nil mant argument is  
    /// provided its value is set to the mantissa of `self`, with the  
    /// same precision and rounding mode as `self`. The components  
    /// satisfy `self` == mant × 2**exp, with 0.5 <= |mant| < 1.0.  
    /// Calling mant_exp with a nil argument is an efficient way to  
    /// get the exponent of the receiver.  
    ///  
    /// Special cases are:  
    ///  
    ///	(  ±0).mant_exp(mant) = 0, with mant set to   ±0  
    ///	(±Inf).mant_exp(mant) = 0, with mant set to ±Inf  
    ///  
    /// `self` and mant may be the same in which case `self` is set to its  
    /// mantissa value.  
    pub fn mant_exp(&self) -> (Float, isize) {
        let exp = if self.form.is_finite() {
            self.exp
        } else {
            0
        };
     
        let mut mant = self.deep_clone();
        if mant.form.is_finite() {
            mant.exp = 0;
        }
        
        (mant, exp)
    } 
    
    fn set_exp_and_round(&mut self, exp: isize, sbit: usize) {
        if exp < Self::min_exp() {
            // underflow
            self.acc = Self::make_accuracy(self.neg == Negative);
            self.form = Form::Zero;
        } else if exp > Self::max_exp() {
            // overflow
            self.acc = Self::make_accuracy(self.neg != Negative);
            self.form = Form::Inf;
        } else {
            self.form = Form::Finite;
            self.exp = exp;
            self.round(sbit);
        }
    }

    /// SetMantExp sets z to mant × 2**exp and returns z.  
    /// The result z has the same precision and rounding mode  
    /// as mant. SetMantExp is an inverse of MantExp but does  
    /// not require 0.5 <= |mant| < 1.0. Specifically:  
    ///  
    ///	mant := new(Float)  
    ///	new(Float).SetMantExp(mant, x.MantExp(mant)).Cmp(x) == 0  
    ///  
    /// Special cases are:  
    ///  
    ///	z.SetMantExp(  ±0, exp) =   ±0  
    ///	z.SetMantExp(±Inf, exp) = ±Inf  
    ///  
    /// z and mant may be the same in which case z's exponent  
    /// is set to exp.  
    pub fn set_mant_exp(&mut self, mant: Float, exp: isize) {
        self.mode = mant.mode;
        self.acc = mant.acc;
        self.form = mant.form;
        self.neg = mant.neg;
        self.prec = mant.prec;
        self.exp = mant.exp;
        self.mant.clear();
        self.mant.as_mut_vec().extend(mant.mant.iter());
        
        if self.form.is_finite() {
            self.set_exp_and_round(self.exp.saturating_add(exp), 0);
        }
    }
    
    pub fn is_negative(&self) -> Option<bool> {
        if self.is_nan() {
            None
        } else {
            Some(self.neg == Negative)
        }
    }
    
    pub fn is_infinite(&self) -> Option<bool> {
        if self.is_nan() {
            None
        } else {
            Some(self.form.is_infinite())
        }
    }
    
    /// test `self` whether is integer
    ///
    /// # Notes
    /// 
    /// ±Inf values are not integers
    pub fn is_integer(&self) -> Option<bool> {
        if self.is_nan() {
            None
        } else if !self.form.is_finite() {
            Some(self.form.is_zero())
        } else if self.exp <= 0 {
            Some(false)
        } else {
            // not enough bits for fractional mantissa
            Some(self.prec <= (self.exp as usize) || self.required_min_precision() <= (self.exp as usize))
        }
    }
    
    fn set_bits(&mut self, is_neg: bool, x: u64) {
        if self.prec == 0 {
            self.prec = 64;
        }
        
        self.acc = Accuracy::Exact;
        self.neg = BISign::from(is_neg);
        
        if x == 0 {
            self.form = Form::Zero;
        } else {
            self.form = Form::Finite;

            let s = x.leading_zeros();
            self.mant.clear();
            let tmp = x << s;
            self.mant.as_mut_vec().push((tmp & 0xffffffff) as u32);
            self.mant.as_mut_vec().push((tmp >> 32) as u32);
            self.exp = (64 - s) as isize;
            if self.prec < 64 {
                self.round(0);
            }
        }
    }
    
    fn set_u64(&mut self, x: u64) {
        self.set_bits(false, x);
    }
    
    fn set_i64(&mut self, x: i64) {
        self.set_bits(x < 0, x.abs() as u64)
    }
    
    fn set_f64(&mut self, x: f64) {
        if x.is_nan() {
            self.form = Form::Nan;
        } else {
            if self.prec == 0 {
                self.prec = 53;
            }

            self.acc = Accuracy::Exact;
            self.neg = BISign::from(x.is_sign_negative());
            if x == 0f64 {
                self.form = Form::Zero;
            } else if x.is_infinite() {
                self.form = Form::Inf;
            } else {
                self.form = Form::Finite;
                let (fmant, exp) = util::frexp(x);
                let tmp = (1u64 << 63) | (fmant.to_bits() << 11);
                self.mant.clear();
                self.mant.as_mut_vec().push((tmp & 0xffffffff) as u32);
                self.mant.as_mut_vec().push((tmp >> 32) as u32);
                self.exp = exp;
                if self.prec < 53 {
                    self.round(0);
                }
            }
        }
    }
    
    fn set_float(&mut self, x: &Float) {
        self.acc = Accuracy::Exact;
        self.form = x.form;
        self.neg = x.neg;
        if self.form.is_finite() {
            self.exp = x.exp;
            self.mant.clear();
            self.mant.as_mut_vec().extend(x.mant.iter());
        }
        if self.prec == 0 {
            self.prec = x.prec;
        } else if self.prec < x.prec {
            self.round(0);
        }
    }

    /// fnorm normalizes mantissa m by shifting it to the left  
    /// such that the msb of the most-significant word (msw) is 1.  
    /// It returns the shift amount. It assumes that len(m) != 0.  
    fn fnorm(nat: &mut Nat) -> usize {
        if nat.is_nan() {0}
        else {
            let s = nat.as_vec().last().unwrap().leading_zeros() as usize;
            if s > 0 {
                let c = unsafe {
                    shl_vu_inner(nat.as_mut_vec().as_mut_ptr(), nat.as_vec().as_ptr(), s, nat.as_vec().len())
                };
                assert_eq!(c, 0, "carry must be the 0");
            }
            s
        }
    }
    
    fn make_accuracy(is_above: bool) -> Accuracy {
        if is_above {
            Accuracy::Above
        } else {
            Accuracy::Below
        }
    }
    
    /// round rounds z according to z.mode to z.prec bits and sets z.acc accordingly.
    /// sbit must be 0 or 1 and summarizes any "sticky bit" information one might
    /// have before calling round. z's mantissa must be normalized (with the msb set)
    /// or empty.
    ///
    /// CAUTION: The rounding modes ToNegativeInf, ToPositiveInf are affected by the
    /// sign of z. For correct rounding, the sign of z must be set correctly before
    /// calling round.
    fn round(&mut self, mut sbit: usize) {
        self.acc = Accuracy::Exact;
        
        if !self.form.is_finite() {
            return;
        }
        
        let m = self.mant.as_vec().len();
        let bits = m << 5;
        if bits <= self.prec {
            // mantissa fits => nothing to do
            return;
        }

        // Rounding is based on two bits: the rounding bit (rbit) and the
        // sticky bit (sbit). The rbit is the bit immediately before the
        // z.prec leading mantissa bits (the "0.5"). The sbit is set if any
        // of the bits before the rbit are set (the "0.25", "0.125", etc.):
        //
        //   rbit  sbit  => "fractional part"
        //
        //   0     0        == 0
        //   0     1        >  0  , < 0.5
        //   1     0        == 0.5
        //   1     1        >  0.5, < 1.0

        // bits > z.prec: mantissa too large => round
        let r = bits - self.prec - 1; // rounding bit position; r >= 0
        // rounding bit; be safe and ensure it's a single bit
        let rbit = match self.mant.is_set_bit(r) {
            Some(true) => 1,
            _ => 0,
        };
        // The sticky bit is only needed for rounding ToNearestEven
        // or when the rounding bit is zero. Avoid computation otherwise.
        if sbit == 0 && (rbit == 0 || self.mode == ToNearestEven) {
            sbit = self.mant.sticky(r);
        }
        sbit &= 1; // be safe and ensure it's a single bit

        // cut off extra words
        let n = (self.prec + 31) >> 5; // mantissa length in words for desired precision
        if m > n {
            self.mant.as_mut_vec().rotate_left(m-n); // move n last words to front
            self.mant.as_mut_vec().truncate(n);
        }

        // determine number of trailing zero bits (ntz) and compute lsb mask of mantissa's least-significant word
        let ntz = (n<<5) - self.prec;
        let lsb = 1 << ntz;

        // round if result is inexact
        if (rbit | sbit) != 0 {
            // Make rounding decision: The result mantissa is truncated ("rounded down")
            // by default. Decide if we need to increment, or "round up", the (unsigned)
            // mantissa.
            let mut inc = false;
            inc = match self.mode {
                ToNegativeInf => self.neg == Negative,
                ToZero => inc,
                ToNearestEven => rbit != 0 && (sbit != 0 || (self.mant.as_vec()[0] & lsb) != 0),
                ToNearestAway => rbit != 0,
                AwayFromZero => true,
                ToPositiveInf => self.neg != Negative,
            };

            // A positive result (!z.neg) is Above the exact result if we increment,
            // and it's Below if we truncate (Exact results require no rounding).
            // For a negative result (z.neg) it is exactly the opposite.
            self.acc = Self::make_accuracy(BISign::from(inc) != self.neg);

            unsafe {
                if inc {
                    // add 1 to mantissa
                    if add_vw_inner(self.mant.as_mut_vec().as_mut_ptr(), self.mant.as_vec().as_ptr(), lsb, self.mant.as_vec().len()) != 0 {
                        // mantissa overflow => adjust exponent
                        if self.exp >= Self::max_exp() {
                            // exponent overflow
                            self.form = Form::Inf;
                            return;
                        } else {
                            self.exp += 1;
                            // adjust mantissa: divide by 2 to compensate for exponent adjustment
                            shr_vu_inner(self.mant.as_mut_vec().as_mut_ptr(), self.mant.as_vec().as_ptr(), 1, self.mant.as_vec().len());
                            // set msb == carry == 1 from the mantissa overflow above
                            self.mant.as_mut_vec()[n-1] |= 1 << 31;
                        }
                    }
                }
            }
        }

        // zero out trailing bits in least-significant word
        self.mant.as_mut_vec()[0] &= !(lsb - 1);
    }
    
    fn set_nat(&mut self, x: &Nat, sign: BISign) {
        if x.is_nan() {
            self.form = Form::Nan;
        } else {
            let bits = x.bits_len();
            if self.prec == 0 {
                self.prec = std::cmp::max(bits, 64);
            }
            self.acc = Accuracy::Exact;
            self.neg = sign;
            if x == &0u32 {
                self.form = Form::Zero;
            } else {
                self.mant.clear();
                self.mant.as_mut_vec().extend(x.iter());
                Self::fnorm(&mut self.mant);
                self.set_exp_and_round(bits as isize, 0);
            }
        }
    }

    fn set_bigint(&mut self, x: &BigInt) {
        self.set_nat(&x.nat, x.sign);
    }
    
    fn set_rat(&mut self, x: &Rat) {
        match x.is_integer() {
            Some(true) => {
                self.set_bigint(x.numerator());
            },
            Some(false) => {
                let (mut a, b) = (Float::from(x.numerator().clone()), Float::from(x.denominator().clone()));
                if self.prec == 0 {
                    self.prec = std::cmp::max(a.prec, b.prec);
                }
                a /= b;
                *self = a;
            },
            None => {
                self.form = Form::Nan;
            }
        }
    }
    
    /// $x / y$, ignoring signs of x and y for the division.  
    /// x and y must have a non-empty mantissa and valid exponent.
    fn uquo(&mut self, y: &Float) {
        // mantissa length in words for desired result precision + 1
        // (at least one extra bit so we get the rounding bit after
        // the division)
        let n = (self.prec >> 5) as isize + 1;

        // compute adjusted x.mant such that we get enough result precision
        let d = n - (self.mant.as_vec().len() as isize) + (y.mant.as_vec().len() as isize);
        let xadj = if d > 0 {
            let tmp = self.mant.deep_clone();
            tmp.as_mut_vec().resize(((self.mant.as_vec().len() as isize) + d) as usize, 0);
            tmp
        } else {
            self.mant.clone()
        };

        // Compute d before division since there may be aliasing of x.mant
        // (via xadj) or y.mant with z.mant.
        let d = (xadj.as_vec().len() as isize) - (y.mant.as_vec().len() as isize);

        // divide
        let (quo, rem) = (xadj.clone() / y.mant.clone(), xadj.clone() % y.mant.clone());
        self.mant.clear();
        self.mant.as_mut_vec().extend(quo.iter());
        let e = self.exp - y.exp - ((d - (self.mant.as_vec().len() as isize)) << 5);

        // The result is long enough to include (at least) the rounding bit.
        // If there's a non-zero remainder, the corresponding fractional part
        // (if it were computed), would have a non-zero sticky bit (if it were
        // zero, it couldn't have a non-zero remainder).
        let sbit = if rem > 0u32 {
            1
        } else {
            0
        };

        let s = Self::fnorm(&mut self.mant) as isize;
        self.set_exp_and_round(e - s, sbit);
    }
    
    fn div_inner(&mut self, y: &Float) {
        if self.prec == 0 {
            self.prec = y.prec;
        }

        self.neg = BISign::from(self.neg != y.neg);
        
        if self.form.is_finite() && y.form.is_finite() {
            self.uquo(y)
        } else {
            self.acc = Accuracy::Exact;
            if (self.form.is_zero() && y.form.is_zero()) || (self.form.is_infinite() && self.form.is_infinite()) {
                self.form = Form::Nan;
                self.neg = Natural;
                // panic!("division of zero by zero or infinity by infinity");
            } else if self.form.is_zero() || y.form.is_infinite() {
                self.form = Form::Zero;
            } else {
                self.form = Form::Inf;
            }
        }
    }
    
    fn msb32(nat: &Nat) -> u32 {
        match nat.as_vec().last() {
            Some(&x) => x,
            None => 0,
        }
    }
    
    fn msb64(nat: &Nat) -> u64 {
        let mut itr = nat.iter().rev().take(2);
        match itr.next() {
            Some(&h) => {
                match itr.next() {
                    Some(&l) => ((h as u64) << 32) | (l as u64),
                    None => (h as u64) << 32,
                }
            },
            None => 0,
        }
    }
    
    pub fn truncate_to_u64(&self) -> Option<(u64, Accuracy)> {
        if self.is_nan() {
            None
        } else {
            if self.form.is_finite() {
                if self.neg == Negative {
                    Some((0, Accuracy::Above))
                } else if self.exp <= 0 {
                    // 0 < self < 1
                    Some((0, Accuracy::Below))
                } else if self.exp <= 64 {
                    let u = Self::msb64(&self.mant) >> (64 - self.exp);
                    if self.required_min_precision() <= (self.exp as usize) {
                        Some((u, Accuracy::Exact))
                    } else {
                        Some((u, Accuracy::Below))
                    }
                } else {
                    Some((u64::MAX, Accuracy::Below))
                }
            } else if self.form.is_zero() {
                Some((0, Accuracy::Exact))
            } else {
                // inf
                if self.neg == Negative {
                    Some((0, Accuracy::Above))
                } else {
                    Some((u64::MAX, Accuracy::Below))
                }
            }
        }
    }
    
    pub fn truncate_to_i64(&self) -> Option<(i64, Accuracy)> {
        if self.is_nan() {
            None
        } else {
            if self.form.is_finite() {
                let acc = Self::make_accuracy(self.neg == Negative);
                if self.exp <= 0 {
                    Some((0, acc))
                } else if self.exp <= 63 {
                    let i = (Self::msb64(&self.mant) >> (64 - self.exp)) as i64;
                    let i  = if self.neg == Negative {-i} else {i};
                    if self.required_min_precision() <= (self.exp as usize) {
                        Some((i, Accuracy::Exact))
                    } else {
                        Some((i, acc))
                    }
                } else if self.neg == Negative {
                    // i64::MIN
                    if self.exp == 64 && self.required_min_precision() == 1 {
                        Some((i64::MIN, Accuracy::Exact))
                    } else {
                        Some((i64::MIN, acc))
                    }
                } else {
                    Some((i64::MAX, Accuracy::Below))
                }
            } else if self.form.is_zero() {
                Some((0, Accuracy::Exact))
            } else {
                // inf
                if self.neg == Negative {
                    Some((i64::MIN, Accuracy::Above))
                } else {
                    Some((i64::MAX, Accuracy::Below))
                }
            }
        }
    }
    
    pub fn to_f32(&self) -> (f32, Accuracy) {
        if self.is_nan() {
            (f32::NAN, Accuracy::Exact)
        } else if self.form.is_finite() {
            let (fbits, mbits) = (32, 23);
            let ebits = fbits - mbits - 1;
            //   127  exponent bias
            let bias = (1 << (ebits - 1)) - 1;
            //  -149  smallest unbiased exponent (sub-normal)
            //  -126  smallest unbiased exponent (normal)
            //   127  largest unbiased exponent (normal)
            let (emin, emax) = (1-bias, bias);

            // Float mantissa m is 0.5 <= m < 1.0; compute exponent e for float32 mantissa.
            let e = self.exp - 1; // exponent for normal mantissa m with 1.0 <= m < 2.0

            // Compute precision p for float32 mantissa.
            // If the exponent is too small, we have a denormal number before
            // rounding and fewer than p mantissa bits of precision available
            // (the exponent remains fixed but the mantissa gets shifted right).
            let mut p = mbits + 1; // precision of normal float
            if e < emin {
                // recompute precision
                p = mbits + 1 - emin + e;
                // If p == 0, the mantissa of x is shifted so much to the right
                // that its msb falls immediately to the right of the float32
                // mantissa space. In other words, if the smallest denormal is
                // considered "1.0", for p == 0, the mantissa value m is >= 0.5.
                // If m > 0.5, it is rounded up to 1.0; i.e., the smallest denormal.
                // If m == 0.5, it is rounded down to even, i.e., 0.0.
                // If p < 0, the mantissa value m is <= "0.25" which is never rounded up.
                // m <= 0.5 || m == 0.5
                if p < 0 || (p == 0 && self.mant.sticky((Self::nat_len(&self.mant) << 5) - 1) == 0) {
                    // underflow to ±0
                    if self.neg == Negative {
                        return (-0f32, Accuracy::Above);
                    } else {
                        return (0f32, Accuracy::Below);
                    }
                } else if p == 0 {
                // otherwise, round up
                // We handle p == 0 explicitly because it's easy and because
                // Float.round doesn't support rounding to 0 bits of precision.
                    if self.neg == Negative {
                        return (-f32::MIN_POSITIVE, Accuracy::Below);
                    } else {
                        return (f32::MIN_POSITIVE, Accuracy::Above);
                    }
                }
            }
            
            // p > 0
            // round
            let mut r = Self::default();
            r.prec = p as usize;
            r.set_float(self);
            let e = r.exp - 1;

            // Rounding may have caused r to overflow to ±Inf
            // (rounding never causes underflows to 0).
            // If the exponent is too large, also overflow to ±Inf.
            if r.form.is_infinite() || e > emax {
                // overflow
                if self.neg == Negative {
                    (f32::NEG_INFINITY, Accuracy::Below)
                } else {
                    (f32::INFINITY, Accuracy::Above)
                }
            } else {
                // e <= emax

                // Determine sign, biased exponent, and mantissa.
                let sign = if self.neg == Negative {
                    1u32 << (fbits - 1)
                } else {0};

                // Rounding may have caused a denormal number to
                // become normal. Check again.
                let (bexp, mant) = if e < emin {
                    // denormal number: recompute precision
                    // Since rounding may have at best increased precision
                    // and we have eliminated p <= 0 early, we know p > 0.
                    // bexp == 0 for denormals
                    let p = mbits + 1 - emin + e;
                    let mant = Self::msb32(&r.mant) >> (fbits - p);
                    (0, mant)
                } else {
                    // normal number: emin <= e <= emax
                    let bexp = ((e + bias) << mbits) as u32;
                    let mant = (Self::msb32(&r.mant) >> ebits) & ((1 << mbits) - 1);
                    (bexp, mant)
                };

                (f32::from_bits(sign | bexp | mant), r.acc)
            }
        } else if self.form.is_zero() {
            if self.neg == Negative {
                (-0f32, Accuracy::Exact)
            } else {
                (0f32, Accuracy::Exact)
            }
        } else if self.form.is_infinite() {
            if self.neg == Negative {
                (f32::NEG_INFINITY, Accuracy::Exact)
            } else {
                (f32::INFINITY, Accuracy::Exact)
            }
        } else {
            unreachable!();
        }
    }
    
    pub fn to_f64(&self) -> (f64, Accuracy) {
        if self.is_nan() {
            (f64::NAN, Accuracy::Exact)
        } else if self.form.is_finite() {

            let (fbits, mbits) = (64, 52);
            let ebits = fbits - mbits - 1;
            let bias = (1<<(ebits - 1)) - 1;
            // -1022  smallest unbiased exponent (normal)
            //  1023  largest unbiased exponent (normal)
            let (emin, emax) = (1-bias, bias);

            // Float mantissa m is 0.5 <= m < 1.0; compute exponent e for float64 mantissa.
            // exponent for normal mantissa m with 1.0 <= m < 2.0
            let e = self.exp - 1;

            // Compute precision p for float64 mantissa.
            // If the exponent is too small, we have a denormal number before
            // rounding and fewer than p mantissa bits of precision available
            // (the exponent remains fixed but the mantissa gets shifted right).
            let mut p = mbits + 1;
            if e < emin {
                // recompute precision
                p = mbits + 1 - emin + e;
                // If p == 0, the mantissa of x is shifted so much to the right
                // that its msb falls immediately to the right of the float64
                // mantissa space. In other words, if the smallest denormal is
                // considered "1.0", for p == 0, the mantissa value m is >= 0.5.
                // If m > 0.5, it is rounded up to 1.0; i.e., the smallest denormal.
                // If m == 0.5, it is rounded down to even, i.e., 0.0.
                // If p < 0, the mantissa value m is <= "0.25" which is never rounded up.
                if p < 0 || (p == 0 && self.mant.sticky((Self::nat_len(&self.mant) << 5) - 1) == 0) {
                    // underflow to ±0
                    if self.neg == Negative {
                        return (-0f64, Accuracy::Above);
                    } else {
                        return (0f64, Accuracy::Below);
                    }
                } else if p == 0 {
                    // otherwise, round up
                    // We handle p == 0 explicitly because it's easy and because
                    // Float.round doesn't support rounding to 0 bits of precision.
                    if self.neg == Negative {
                        return (f64::MIN_POSITIVE, Accuracy::Below);
                    } else {
                        return (f64::MIN_POSITIVE, Accuracy::Above);
                    }
                }
            }
            // p > 0

            // round
            let mut r = Self::default();
            r.prec = p as usize;
            r.set_float(self);
            let e = r.exp - 1;

            // Rounding may have caused r to overflow to ±Inf
            // (rounding never causes underflows to 0).
            // If the exponent is too large, also overflow to ±Inf.
            if r.form.is_infinite() || e > emax {
                // overflow
                if self.neg == Negative {
                    (f64::NEG_INFINITY, Accuracy::Below)
                } else {
                    (f64::INFINITY, Accuracy::Above)
                }
            } else {
                let sign = if self.neg == Negative {
                    1 << (fbits - 1)
                } else {0};
                
                // Rounding may have caused a denormal number to
                // become normal. Check again.
                let (bexp, mant) = if e < emin {
                    // denormal number: recompute precision
                    // Since rounding may have at best increased precision
                    // and we have eliminated p <= 0 early, we know p > 0.
                    // bexp == 0 for denormals
                    let p = mbits + 1 - emin + e;
                    let mant = Self::msb64(&r.mant) >> (fbits - p);
                    (0, mant)
                } else {
                    // normal number: emin <= e <= emax
                    let bexp = (e + bias) << mbits;
                    let mant = (Self::msb64(&r.mant) >> ebits) & ((1 << mbits) - 1);
                    (bexp as u64, mant)
                };

                (f64::from_bits(sign | bexp | mant), r.acc)
            }
        } else if self.form.is_zero() {
            if self.neg == Negative {
                (-0f64, Accuracy::Exact)
            } else {
                (0f64, Accuracy::Exact)
            }
        } else if self.form.is_infinite() {
            if self.neg == Negative {
                (f64::NEG_INFINITY, Accuracy::Exact)
            } else {
                (f64::INFINITY, Accuracy::Exact)
            }
        } else {
            unreachable!();
        }
    }
    
    pub fn abs(&self) -> Float {
        let mut z = self.deep_clone();
        z.neg = Natural;
        z
    }
    
    #[inline]
    fn nat_len(nat: &Nat) -> usize {
        nat.as_vec().len()
    }
    
    fn nan() -> Float {
        let mut z = Self::default();
        z.form = Form::Nan;
        z
    }
    
    fn set_nan(&mut self) {
        self.form = Form::Nan;
    }
    
    fn uadd(&mut self, y: &Float) {
        // Note: This implementation requires 2 shifts most of the
        // time. It is also inefficient if exponents or precisions
        // differ by wide margins. The following article describes
        // an efficient (but much more complicated) implementation
        // compatible with the internal representation used here:
        //
        // Vincent Lefèvre: "The Generic Multiple-Precision Floating-
        // Point Addition With Exact Rounding (as in the MPFR Library)"
        // http://www.vinc17.net/research/papers/rnc6.pdf

        let x = self;

        // compute exponents ex, ey for mantissa with "binary point"
        // on the right (mantissa.0) - use int64 to avoid overflow
        let (ex, ey) = (x.exp - ((Self::nat_len(&x.mant) as isize) << 5),
            y.exp - ((Self::nat_len(&y.mant) as isize) << 5));

        let exp= if ex < ey {
            let tmp = y.mant.clone() << ((ey - ex) as usize);
            x.mant += tmp;
            ex
        } else if ex > ey {
            x.mant <<= (ex - ey) as usize;
            x.mant += y.mant.clone();
            ey
        } else {
            x.mant += y.mant.clone();
            ex
        };

        let tmp = exp + ((Self::nat_len(&x.mant) << 5) as isize) - (Self::fnorm(&mut x.mant) as isize);
        x.set_exp_and_round(tmp, 0);
    }
    
    fn add_inner(&mut self, y: &Float) {
        if self.prec == 0 {
            self.prec = y.prec;
        }
        
        if self.form.is_finite() && y.form.is_finite() {
            // x + y (common case)

            // Below we set z.neg = x.neg, and when z aliases y this will
            // change the y operand's sign. This is fine, because if an
            // operand aliases the receiver it'll be overwritten, but we still
            // want the original x.neg and y.neg values when we evaluate
            // x.neg != y.neg, so we need to save y.neg before setting z.neg.
            let yneg = y.neg;

            if self.neg == yneg {
                // x + y == x + y
                // (-x) + (-y) == -(x + y)
                self.uadd(y);
            } else {
                // x + (-y) == x - y == -(y - x)
                // (-x) + y == y - x == -(x - y)
                if self.ucmp(y) > 0 {
                    self.usub(y);
                } else {
                    let mut tmp = y.deep_clone();
                    tmp.neg = !self.neg;
                    tmp.usub(&*self);
                    *self = tmp;
                }
            }
            
            if self.form.is_zero() && self.mode == RoundingMode::ToNegativeInf && self.acc == Accuracy::Exact {
                self.neg = Negative;
            }
        } else if self.form.is_infinite() && y.form.is_infinite() && self.neg != y.neg {
            // +Inf + -Inf
            // -Inf + +Inf
            // value of z is undefined but make sure it's valid
            self.acc = Accuracy::Exact;
            self.form = Form::Nan;
            self.neg = BISign::from(false);
            // panic!("addition of infinities with opposite signs");
        } else if self.form.is_infinite() || y.form.is_zero() {
            // ±Inf + y
            // x + ±0
        } else {
            // ±0 + y
            // x + ±Inf
            self.set_float(y);
        }
    }
    
    fn usub(&mut self, y: &Float) {
        // This code is symmetric to uadd.
        // We have not factored the common code out because
        // eventually uadd (and usub) should be optimized
        // by special-casing, and the code will diverge.
        let x = self;
        
        let (ex, ey) = (
            x.exp - ((Self::nat_len(&x.mant) << 5) as isize),
            y.exp - ((Self::nat_len(&y.mant) << 5) as isize),
            );
        
        let exp = if ex < ey {
            let tmp = y.mant.clone() << ((ey - ex) as usize);
            x.mant -= tmp;
            ex
        } else if ex > ey {
            x.mant <<= (ex - ey) as usize;
            x.mant -= y.mant.clone();
            ey
        } else {
            x.mant -= y.mant.clone();
            ex
        };

        // operands may have canceled each other out
        if x.mant == 0u32 {
            x.acc = Accuracy::Exact;
            x.form = Form::Zero;
            x.neg = Natural;
        } else {
            let tmp = exp + ((Self::nat_len(&x.mant) << 5) as isize) - (Self::fnorm(&mut x.mant) as isize);
            x.set_exp_and_round(tmp, 0);
        }
    }
    
    fn sub_inner(&mut self, y: &Float) {
        if self.prec == 0 {
            self.prec = y.prec;
        }

        if self.form.is_finite() && y.form.is_finite() {
            // x - y (common case)
            let yneg = y.neg;
            if self.neg != yneg {
                // x - (-y) == x + y
                // (-x) - y == -(x + y)
                self.uadd(y);
            } else {
                // x - y == x - y == -(y - x)
                // (-x) - (-y) == y - x == -(x - y)
                if self.ucmp(y) > 0 {
                    self.usub(y);
                } else {
                    let mut tmp = y.deep_clone();
                    tmp.neg = !self.neg;
                    tmp.usub(&*self);
                    *self = tmp;
                }
            }
            if self.form.is_zero() && self.mode == RoundingMode::ToNegativeInf && self.acc == Accuracy::Exact {
                self.neg = Negative;
            }
        } else if self.form.is_infinite() && y.form.is_infinite() && self.neg == y.neg {
            // +Inf - +Inf
            // -Inf - -Inf
            // value of z is undefined but make sure it's valid
            self.acc = Accuracy::Exact;
            self.form = Form::Nan;
            self.neg = Natural;
            // panic!("subtraction of infinities with equal signs");
        } else if self.form.is_zero() && y.form.is_zero() {
            // ±0 - ±0
            self.acc = Accuracy::Exact;
            self.form = Form::Zero;
            // -0 - +0 == -0
            self.neg = BISign::from(self.neg == Negative && y.neg != Negative);
        } else if self.form.is_infinite() || y.form.is_zero() {
            // ±Inf - y
            // x - ±0
        } else {
            // ±0 - y
            // x - ±Inf
            self.set_float(y);
        }
    }
    
    fn umul(&mut self, y: &Float) {
        let x = self;
        // Note: This is doing too much work if the precision
        // of z is less than the sum of the precisions of x
        // and y which is often the case (e.g., if all floats
        // have the same precision).

        let e = x.exp + y.exp;
        x.mant *= y.mant.clone();
        
        let tmp = e - (Self::fnorm(&mut x.mant) as isize);
        x.set_exp_and_round(tmp, 0);
    }
    
    fn mul_inner(&mut self, y: &Float) {
        if self.prec == 0 {
            self.prec = y.prec;
        }

        self.neg = BISign::from(self.neg != y.neg);

        if self.form.is_finite() && y.form.is_finite() {
            // x * y (common case)
            self.umul(y);
        } else {
            self.acc = Accuracy::Exact;
            if (self.form.is_zero() && y.form.is_infinite()) || (self.form.is_infinite() && y.form.is_zero()) {
                // ±0 * ±Inf
                // ±Inf * ±0
                // value of z is undefined but make sure it's valid
                self.form = Form::Nan;
                self.neg = Natural;
                // panic!("multiplication of zero with infinity");
            } else if self.form.is_infinite() || y.form.is_infinite() {
                // ±Inf * y
                // x * ±Inf
                self.form = Form::Inf;
            } else {
                // ±0 * y
                // x * ±0
                self.form = Form::Zero;
            }
        }
    }

    /// ucmp returns -1, 0, or +1, depending on whether 
    /// |x| < |y|, |x| == |y|, or |x| > |y|.
    fn ucmp(&self, y: &Float) -> isize {
        let x = self;

        if x.exp < y.exp {
            -1
        } else if x.exp > y.exp {
            1
        } else {
            let (mut i, mut j) = (Self::nat_len(&x.mant), Self::nat_len(&y.mant));
            while i > 0 || j > 0 {
                let xm = if i > 0 {
                    i -= 1;
                    x.mant.as_vec()[i]
                } else {
                    0
                };
                
                let ym = if j > 0 {
                    j -= 1;
                    y.mant.as_vec()[j]
                } else {
                    0
                };
                
                if xm < ym {
                    return -1;
                } else if xm > ym {
                    return 1;
                }
            }
            
            0
        }
    }

    ///	-2 if -Inf == self
    ///	-1 if -Inf < self < 0
    ///	 0 if self == 0 (signed or unsigned)
    ///	+1 if 0 < self < +Inf
    ///	+2 if self == +Inf
    fn ord(&self) -> Option<isize> {
        let m = if self.form.is_finite() {
            Some(1)
        } else if self.form.is_zero() {
            Some(0)
        } else if self.form.is_infinite() {
            Some(2)
        } else {
            None
        };
        
        if self.neg == Negative {
            m.map(|x| {-x})
        } else {
            m
        }
    }

    ///   -1 if self <  other
    ///    0 if self == other (incl. -0 == 0, -Inf == -Inf, and +Inf == +Inf)
    ///   +1 if self >  other
    /// 
    fn cmp_inner(&self, other: &Float) -> Option<isize> {
        let (left, right) = (self.ord(), other.ord());
        left.zip(right).map(|(mx, my)| {
            if mx < my {
                -1
            } else if mx > my {
                1
            } else {
                if mx == -1 {
                    other.ucmp(self)
                } else if mx == 1 {
                    self.ucmp(other)
                } else {
                    0
                }
            }
        })
    }
}

impl Neg for Float {
    type Output = Self; 

    fn neg(self) -> Self::Output {
        let mut z = self.deep_clone();
        z.neg = !z.neg;
        z
    }
}

impl Default for Float {
    /// +0.0
    fn default() -> Self {
        Float {
            mode: RoundingMode::ToNearestEven,
            acc: Accuracy::Exact,
            form: Form::Zero,
            neg: BISign::from(false),
            prec: 0,
            exp: 0,
            mant: Nat::nan(),
        }
    }
}

float_impl_from_basic!(set_u64, u64, u8, u16, u32, u64);
float_impl_from_basic!(set_i64, i64, i8, i16, i32, i64);
float_impl_from_basic!(set_f64, f64, f32, f64);

impl From<BigInt> for Float {
    fn from(x: BigInt) -> Self {
        let mut z = Self::default();
        z.set_bigint(&x);
        z
    }
}


impl From<Nat> for Float {
    fn from(x: Nat) -> Self {
        let mut z = Self::default();
        z.set_nat(&x, Natural);
        z
    }
}

impl From<Rat> for Float {
    fn from(x: Rat) -> Self {
        let mut z = Self::default();
        z.set_rat(&x);
        z
    }
}

impl Div for Float {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        if self.is_nan() || rhs.is_nan() {
            Self::nan()
        } else {
            let mut z = self.deep_clone();
            z.div_inner(&rhs);
            z
        }
    }
}

impl DivAssign for Float {
    fn div_assign(&mut self, rhs: Self) {
        if self.is_nan() || rhs.is_nan() {
            self.set_nan();
        } else {
            self.div_inner(&rhs);
        }
    }
}

impl Add for Float {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        if self.is_nan() || rhs.is_nan() {
            Self::nan()
        } else {
            let mut z = self.deep_clone();
            z.add_inner(&rhs);
            z
        }
    }
}

impl AddAssign for Float {
    fn add_assign(&mut self, rhs: Self) {
        if self.is_nan() || rhs.is_nan() {
            self.set_nan();
        } else {
            self.add_inner(&rhs);
        }
    }
}

impl Sub for Float {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        if self.is_nan() || rhs.is_nan() {
            Self::nan()
        } else {
            let mut z = self.deep_clone();
            z.sub_inner(&rhs);
            z
        }
    }
}

impl SubAssign for Float {
    fn sub_assign(&mut self, rhs: Self) {
        if self.is_nan() || rhs.is_nan() {
            self.set_nan();
        } else {
            self.sub_inner(&rhs);
        }
    }
}

impl Mul for Float {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        if self.is_nan() || rhs.is_nan() {
            Self::nan()
        } else {
            let mut z= self.deep_clone();
            z.mul_inner(&rhs);
            z
        }
    }
}

impl MulAssign for Float {
    fn mul_assign(&mut self, rhs: Self) {
        if self.is_nan() || rhs.is_nan() {
            self.set_nan();
        } else {
            self.mul_inner(&rhs);
        }
    }
}

impl PartialEq for Float {
    fn eq(&self, other: &Self) -> bool {
        match self.cmp_inner(other) {
            Some(x) => x == 0,
            None => false,
        }
    }
}

impl PartialOrd for Float {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.cmp_inner(other).map(|x| {
            if x > 0 {
                Ordering::Greater
            } else if x < 0 {
                Ordering::Less
            } else {
                Ordering::Equal
            }
        })
    }
}


