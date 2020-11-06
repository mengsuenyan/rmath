/// 自然数

use std::rc::Rc;
use std::str::FromStr;
use crate::bigint::nat_err::NatError;
use crate::parse_err::ParseErrKind::{BeginWithIllegalChar, IllegalCharEncounter};
use std::fmt::{Debug, Binary, LowerHex, UpperHex, Octal, Formatter, Display};
use std::cell::Cell;
use std::cmp::Ordering;
use std::ops::{Add, AddAssign, SubAssign, Sub, ShrAssign, Shr, Shl, ShlAssign, 
    Div, DivAssign, Mul, MulAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign,
    BitXor, BitXorAssign, Not, Rem, RemAssign};
use crate::rand::IterSource;
use crate::bigint::arith::{add_mul_vvw, sub_vv_inner, add_vv_inner, add_vw_inner, sub_vw_inner, add_mul_vvw_inner, mul_ww, shl_vu_inner, mul_add_vww, add_vv};
use crate::bigint::BigInt;

const KARATSUBA_THRESHOLD: usize = 40;
const BASIC_SQRT_HRESHOLD: usize = 20;
const KARATSUBA_SQRT_HRESHOLD: usize = 260;

#[cfg(test)]
mod tests;

/// The type `Nat` provides natural number operations like the Add, Sub, Mul, Div and so on.
/// 
/// # Examples
/// 
/// ```Rust
/// use rmath::bigint::Nat;
/// use std::str::FromStr;
/// 
/// let (a, b) = (Nat::from(u32::MAX), Nat::from(u32::MAX));
/// let sum = a.clone() + b.clone();
/// let mul = sum * a.clone() + b.clone();
/// println!("(({}+{})*{}) + {} = {}", a, b, a, b, mul);
/// 
/// let a = Nat::from_str("2938462938472983472983659726349017249287491026512746239764525612965293865296239471239874193284792387498274256129746192347").unwrap();
/// let b = Nat::from_str("298472983472983471903246121093472394872319615612417471234712061").unwrap();
/// println!("{} * {} = {}", a.clone(), b.clone(), a*b );
/// ```
/// Note: The implementation of the `Clone` trait just only provide a shadow clone of the data that purpose 
/// is to share the ownership of the data, and the `deep_clone` method provide a real clone of the data.
/// 
/// # Panics
/// 
/// The panic will occurred when the divisor or modulus is 0 in the `/` or `%` operation;
#[derive(Clone)]
pub struct Nat {
    nat: Rc<Cell<Vec<u32>>>,
}

impl Nat {
    pub(super) fn as_vec(&self) -> &Vec<u32> {
        unsafe {self.nat.as_ptr().as_ref().unwrap()}
    }
    
    pub(super) fn as_mut_vec(&self) -> &mut Vec<u32> {
        unsafe {self.nat.as_ptr().as_mut().unwrap()}
    }
    
    pub(super) fn as_slice(&self) -> &[u32] {
        self.as_vec().as_slice()
    }

    #[allow(unused)]
    pub(super) fn to_vec(&self) -> Vec<u32> {
        self.as_vec().clone()
    }

    #[allow(unused)]
    pub(super) fn into_vec(self) -> Vec<u32> {
        self.nat.take()
    }
    
    #[allow(unused)]
    pub(super) fn as_mut_slice(&self) -> &mut [u32] {
        self.as_mut_vec().as_mut_slice()
    }
    
    pub(super) fn iter(&self) -> std::slice::Iter<'_, u32> {
        self.as_slice().iter()
    }
    
    pub(super) fn iter_mut(&self) -> std::slice::IterMut<'_, u32> {
        self.as_mut_slice().iter_mut()
    }
    
    pub(super) fn clear(&mut self) {
        self.as_mut_vec().clear();
    }
    
    pub fn deep_clone(&self) -> Self {
        Nat::from(self.as_slice())
    }
    
    pub fn is_nan(&self) -> bool {
        self.as_vec().is_empty()
    }
    
    #[inline]
    pub(super) fn num(&self) -> usize {
        self.as_vec().len()
    }

    fn from_le_or_be_bytes<'a>(data: impl DoubleEndedIterator<Item=&'a u8> + ExactSizeIterator<Item=&'a u8>) -> Nat {
        let (mut val, mut nat) = (0u32, Vec::with_capacity(data.len()));

        for (i, &e) in data.enumerate() {
            let j = i & 3;
            val |= (e as u32) << (j << 3);

            if j == 3 {
                nat.push(val);
                val = 0;
            }
        }

        if val > 0 {
            nat.push(val);
        } else if nat.is_empty() {
            nat.push(0);
        }

        Self::trim_head_zero_(&mut nat);

        Self {
            nat: Rc::new(Cell::new(nat)),
        }
    }

    /// This method is the same as `From<&[u8]>`
    pub fn from_le_bytes(data: &[u8]) -> Nat {
        if data.is_empty() {
            Self::nan()
        } else {
            Self::from_le_or_be_bytes(data.iter())
        }
    }

    /// big endian
    pub fn from_be_bytes(data: &[u8]) -> Nat {
        if data.is_empty() {
            Self::nan()
        } else {
            Self::from_le_or_be_bytes(data.iter().rev())
        }
    }
    
    /// little endian
    pub fn copy_to_le(&self, dst: &mut Vec<u8>) {
        dst.clear();
        if self.is_nan() {
            return;
        }
        
        self.iter().take(self.num().saturating_sub(1)).for_each(|&x| {
            for &y in x.to_le_bytes().iter() {
                dst.push(y);
            };
        });
        
        match self.iter().last() {
            Some(&x) => {
                let i = if x > 0xffffffu32 {4} else if x > 0xffffu32 {3} else if x > 0xffu32 {2} else {1};
                for &y in x.to_le_bytes().iter().take(i) {
                    dst.push(y);
                }
            },
            None => {},
        }
    }
    
    /// little endian
    pub fn to_le_bytes(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(self.num() << 2);
        self.copy_to_le(&mut v);
        v
    }
    
    /// big endian
    pub fn copy_to_be(&self, dst: &mut Vec<u8>) {
        dst.clear();
        if self.is_nan() {
            return;
        }
        
        match self.iter().last() {
            Some(&x) => {
                let i = if x > 0xffffffu32 {0} else if x > 0xffffu32 {1} else if x > 0xffu32 {2} else {3};
                for &y in x.to_be_bytes().iter().skip(i) {
                    dst.push(y);
                }
            },
            None => {},
        }
        
        self.iter().rev().skip(1).for_each(|&x| {
            x.to_be_bytes().iter().for_each(|&y| {dst.push(y);});
        });
    }
    
    /// big endian
    pub fn to_be_bytes(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(self.num() << 2);
        self.copy_to_be(&mut v);
        v
    }
    
    pub fn bits_len(&self) -> usize {
        match self.as_vec().last() {
            Some(&x) if x == 0 => {
                if self.as_vec().len() == 1 {1} else {(self.as_vec().len() - 1) << 5}
            },
            Some(&x) => {
                ((32 - x.leading_zeros()) as usize) + ((self.as_vec().len() - 1) << 5)
            },
            None => 0,
        }
    }
    
    pub(super) fn trim_head_zero_(v: &mut Vec<u32>) {
        let mut i = 0;
        for &ele in v.iter().skip(1).rev() {
            if ele != 0 {
                break;
            }
            i += 1;
        }

        v.truncate(v.len() - i);
    }

    pub(super) fn trim_head_zero(&mut self) {
        Self::trim_head_zero_(self.as_mut_vec());
    }
    
    pub(super) fn min_max<'a>(&'a self, other: &'a Self) -> (&'a Self, &'a Self, bool) {
        if self < other {
            (self, other, false)
        } else {
            (other, self, true)
        }
    }
    
    /// same as the operator `&^` in the golang
    pub fn and_not(self, rhs: Nat) -> Nat {
        let mut nat = self.deep_clone();
        nat.and_not_assign(rhs);
        nat
    }
    
    pub fn and_not_assign(&mut self, rhs: Nat) {
        self.iter_mut().zip(rhs.iter()).for_each(|(x, &y) | {
            *x = (*x) & (!y);
        });
        
        self.trim_head_zero();
    }

    fn check_base(s: &str) -> Result<(usize, usize), NatError> {
        let (mut i, mut itr) = (0, s.chars());
        while let Some(c) = itr.next() {
            if c != '+' {
                if c != ' ' {
                    return if c >= '0' && c <= '9' {
                        match itr.next() {
                            Some(x) => {
                                if c == '0' {
                                    if x == 'o' {
                                        Ok((i+2,8))
                                    } else if x == 'b' || x == 'B' {
                                        Ok((i+2, 2))
                                    } else if x == 'x' || x == 'X' {
                                        Ok((i+2, 16))
                                    } else {
                                        Err(NatError::new(BeginWithIllegalChar, format!("begin with illegal char {}{}", c,x)))
                                    }
                                } else {
                                    Ok((i, 10))
                                }
                            },
                            None => Ok((i, 10)),
                        }
                    } else {
                        Err(NatError::new(BeginWithIllegalChar, format!("begin with illegal char {}", c)))
                    };
                }
            }
            i += 1;
        }
        
        if s.len() > 0 {
            Err(NatError::new(BeginWithIllegalChar, "all char is +"))
        } else {
            Err(NatError::new(BeginWithIllegalChar, "empty string"))
        }
    }
    
    fn from_dec_str(s: &str) -> Result<Self, NatError> {
        if s.is_empty() {return Ok(Nat::from(Vec::<u32>::new()));}
        
        let s = s.trim_start_matches('0');
        if s.is_empty() { return Ok(Nat::from(0u32));}
        
        const ZERO: u32 = '0' as u32;
        let mut v = Vec::with_capacity(s.len());
        
        for c in s.chars() {
            if !c.is_ascii_digit() {
                return Err(NatError::new(IllegalCharEncounter, format!("illegal char {}", c)));
            }
            v.push((c as u32) - ZERO);
        }
        
        let mut nat = Nat::from(0u32);
        v.iter().for_each(|&ele| {
            let tmp = nat.clone() << 1;
            nat <<= 3;
            nat += tmp;
            nat += Nat::from(ele);
        });
        
        Ok(nat)
    }
    
    fn from_bin_str(s: &str) -> Result<Self, NatError> {
        let mut tmp = 0u32;
        let mut v = Vec::with_capacity(s.len() >> 5);
        for (i, c) in s.chars().rev().enumerate() {
            let x = if c == '0' {0} else if c == '1' {1} else {
                return Err(NatError::new(IllegalCharEncounter, format!("illegal char {}", c)));
            };
            
            tmp += x << (i & 31);
            if (i & 31) == 31 {
                v.push(tmp);
                tmp = 0;
            }
        }
        
        if tmp > 0{v.push(tmp);} else {if !s.is_empty() {v.push(tmp);}}
        
        Ok(Nat::from(v))
    }
    
    fn from_oct_str(s: &str) -> Result<Self, NatError> {
        const ZERO: u32 = '0' as u32;
        let (mut i, mut tmp) = (0, 0);
        let mut v = Vec::with_capacity(s.len() / 10);
        
        for c in s.chars().rev() {
            if c >= '0' && c <= '7' {
                let n = (c as u32) - ZERO;

                if (i + 3) >= 32 {
                    tmp += (((1 << (32 - i)) - 1) & n) << i;
                    v.push(tmp);
                    tmp = n >> (32 - i);
                    i = (i + 3) - 32;
                } else {
                    tmp += n << i;
                    i += 3;
                }
            } else {
                return Err(NatError::new(IllegalCharEncounter, format!("illegal char {}", c)));
            }
        }

        if tmp > 0 {v.push(tmp);} else {if !s.is_empty() {v.push(tmp);}}
        Ok(Nat::from(v))
    }
    
    fn from_hex_str(s: &str) -> Result<Self, NatError> {
        const ZERO: u32 = '0' as u32;
        const LA: u32 = 'a' as u32;
        const BA: u32 = 'A' as u32;
        let mut tmp = 0;
        let mut v = Vec::with_capacity(s.len() >> 3);
        
        for (i, c) in s.chars().rev().enumerate() {
            let n = if c >= '0' && c <= '9' {(c as u32) - ZERO}
                else if c >= 'a' && c <= 'f' {((c as u32) - LA) + 10}
                else if c >= 'A' && c <= 'F' {((c as u32) - BA) + 10}
                else {return Err(NatError::new(IllegalCharEncounter, format!("illegal char {}", c)))};
            
            tmp += n << ((i & 7) << 2);
            if (i & 7) == 7 {
                v.push(tmp);
                tmp = 0;
            }
        }
        
        if tmp > 0 {v.push(tmp);} else {if !s.is_empty() {v.push(tmp);}}
        Ok(Nat::from(v))
    }

    /// (abs(self-rhs), self >= rhs)
    pub fn sub_with_sign(&self, rhs: Self) -> (Nat, bool) {
        if self.is_nan() || rhs.is_nan() {
            (Nat::default(), false)
        } else {
            let mut nat = self.deep_clone();
            let x = nat.sub_inner_with_sign(&rhs);
            (nat, x)
        }
    }
    
    /// self -= rhs;
    /// self >= rhs
    pub fn sub_assign_with_sign(&mut self, rhs: Self) -> bool {
        if self.is_nan() || rhs.is_nan() {
            self.clear();
            false
        } else {
            self.sub_inner_with_sign(&rhs)
        }
    }
    
    pub(super) fn partial_cmp_inner(&self, rhs: &Self) -> Ordering {
        if self.num() < rhs.num() {
            Ordering::Less
        } else if self.num() > rhs.num() {
            Ordering::Greater
        } else {
            for (a, b) in self.iter().rev().zip(rhs.iter().rev()) {
                if a < b {
                    return Ordering::Less;
                } else if a > b {
                    return Ordering::Greater;
                }
            }
            Ordering::Equal
        }
    }
    
    pub(super) fn shl_inner(&mut self, rhs: &usize) {
        let rhs = *rhs;
        let (num, nom) = (rhs >> 5, rhs & 31);
        let v = self.as_mut_vec();
        
        if nom > 0 {
            let (nom_c, mut pre) = (32 - nom, 0);
            self.iter_mut().for_each(|a| {
                let tmp = pre;
                pre = (*a) >> nom_c;
                *a = ((*a) << nom) | tmp;
            });
            if pre > 0 {v.push(pre);}
        }
        
        if num > 0 {
            v.resize(v.len() + num, 0);
            v.rotate_right(num);
        }
    }

    pub(super) fn shr_inner(&mut self, rhs: &usize) {
        let rhs = *rhs;
        let v = self.as_mut_vec();
        let (num, nom, nom_c) = (rhs >> 5, rhs & 31, 32 - (rhs & 31));
        let (nom, nom_c) = (nom as u32, nom_c as u32);
        
        if num >= v.len() {
            v.clear();
            v.push(0);
            return;
        }

        let lhs = self.clone();
        let mut pre = 0;
        if nom > 0 {
            let mask_h: u32 = ((1 << nom) - 1) << nom_c;
            let mask_l: u32 = (1 << nom_c) - 1;
            let mut itr = lhs.iter().skip(num);
            match itr.next() { 
                Some(x) => pre = *x >> nom,
                None => {},
            };
            v.iter_mut().zip(itr).for_each(|(a, &b)| {
                let r = b.rotate_right(nom);
                *a = (r & mask_h) | pre;
                pre = r & mask_l;
            });
        }
        v.truncate(v.len() - num);
        if pre > 0 {
            match v.last_mut() {
                Some(x) => *x = pre,
                _ => {},
            };
        } else {
            if nom > 0 && num == 0 {
                v.pop();
                if v.len() == 0 {
                    v.push(0);
                }
            }
        }
    }
    
    #[inline]
    pub(super) fn u32_shl(&mut self, lhs: u32, rhs: usize) {
        let (num, rem) = (rhs >> 5, rhs & 31);
        let v = self.as_mut_vec();
        v.clear();
        v.resize(num, 0);
        v.push(lhs << rem);
    }

    pub(super) fn div_inner(&mut self, rhs: &Self) {
        assert_ne!(rhs, &0u32, "The divisor must not be 0");
        
        if self.nat.as_ptr() == rhs.nat.as_ptr() {
            self.clear();
            self.as_mut_vec().push(1);
            return;
        }
        
        let mut sc = self.deep_clone();
        self.clear();
        
        if sc.partial_cmp_inner(rhs) == Ordering::Less {
            self.as_mut_vec().push(0);
            return;
        }
        
        let (dividend_len, divisor_len) = (sc.bits_len(), rhs.bits_len());
        if dividend_len == divisor_len {
            self.as_mut_vec().push(1);
            return;
        }

        let mut one = Nat::from(1u32);
        let mut den = Nat::with_capacity(rhs.num());
        self.as_mut_vec().push(0);
        loop {
            if !(sc.partial_cmp_inner(rhs) == Ordering::Less) {
                den.clear();
                let mut shift = sc.bits_len() - divisor_len;
                den.as_mut_vec().extend_from_slice(rhs.as_slice());
                den.shl_inner(&shift);
                while den.partial_cmp_inner(&sc) == Ordering::Greater {
                    den.shr_inner(&1);
                    shift -= 1;
                }

                sc.sub_inner(&den);
                one.u32_shl(1, shift);
                self.add_inner(&one);
            } else {
                break;
            }
        }
    }
    
    pub(super) fn rem_inner(&mut self, rhs: &Self) {
        assert_ne!(rhs, &0u32, "The modulus must not be 0");

        if self.partial_cmp_inner(rhs) == Ordering::Less {
            return;
        }

        let divisor_len = rhs.bits_len();
        let mut den = Nat::with_capacity(rhs.num());
        loop {
            if self.partial_cmp_inner(rhs) == Ordering::Less {
                break;
            } else {
                den.clear();
                let shift = self.bits_len() - divisor_len;
                den.as_mut_vec().extend_from_slice(rhs.as_slice());
                den.shl_inner(&shift);
                if self.partial_cmp_inner(&den) == Ordering::Less {
                    den.shr_inner(&1);
                }
                self.sub_inner(&den);
            }
        }
        self.trim_head_zero();
    }

    pub(super) fn bitand_inner(&mut self, rhs: &Self) {
        self.iter_mut().zip(rhs.iter()).for_each(|(a,&b)| {
            *a &= b;
        });
        self.as_mut_vec().truncate(std::cmp::min(self.num(), rhs.num()));
        self.trim_head_zero();
    }
    
    pub(super) fn bitor_inner(&mut self, rhs: &Self) {
        self.iter_mut().zip(rhs.iter()).for_each(|(a, &b)| {
            *a |= b;
        });
        
        let (mi, ma) = (self.num(), rhs.num());
        if mi < ma {
            let v = self.as_mut_vec();
            rhs.iter().skip(mi).for_each(|&b| {
                v.push(b);
            });
        }
    }
    
    pub(super) fn bitxor_inner(&mut self, rhs: &Self) {
        self.iter_mut().zip(rhs.iter()).for_each(|(a, &b)| {
            *a ^= b;
        });

        let (mi, ma) = (self.num(), rhs.num());
        if mi < ma {
            let v = self.as_mut_vec();
            rhs.iter().skip(mi).for_each(|&b| {
                v.push(b);
            });
        }
        self.trim_head_zero();
    }
    
    pub(super) fn mul_inner_basic(&mut self, rhs: &u32) {
        let mut pre = 0;
        const MASK: u64 = u32::MAX as u64;
        
        let rhs = *rhs as u64;
        self.iter_mut().for_each(|a| {
            let x = (*a as u64) * rhs;
            let val = (x & MASK) + pre;
            *a = (val & MASK) as u32;
            pre = (val >> 32) + (x >> 32);
        });
        
        if pre > MASK {
            self.as_mut_vec().push((pre & MASK) as u32);
            self.as_mut_vec().push((pre >> 32) as u32);
        } else {
            self.as_mut_vec().push(pre as u32);
        }
    }
    
    pub(super) fn div_inner_basic(&mut self, rhs: &u32) {
        assert_ne!(rhs, &0, "divisor cannot be the 0");
        
        if self.num() <= 1 {
            match self.as_mut_vec().last_mut() { 
                Some(x) => *x = *x / *rhs,
                None => {},
            };
            return;
        }
        
        let old_len = self.num();
        let rhs = (*rhs) as u64;
        let (mut pre, mut i) = (0, 0);
        self.iter_mut().rev().for_each(|x| {
            let val = (pre << 32) + (*x as u64);
            *x = (val / rhs) as u32;
            pre = val % rhs;
            i += 1;
        });
        
        if i == 0 {
            self.clear();
            self.as_mut_vec().push(0);
        } else {
            self.as_mut_vec().rotate_right(old_len - i);
            self.as_mut_vec().truncate(i);
            self.trim_head_zero();
        }
    }

    pub(super) fn rem_inner_basic(&mut self, rhs: &u32) {
        assert_ne!(rhs, &0, "modulus cannot be the 0");
        
        if self.num() <= 1 {
            match self.as_mut_vec().last_mut() {
                Some(x) => *x = *x % *rhs,
                None => {},
            };
            return;
        }
        
        let mut pre = 0;
        let rhs = (*rhs) as u64;
        self.iter().rev().for_each(|&x| {
            let val = (pre << 32) + (x as u64);
            pre = val % rhs;
        });

        self.clear();
        self.as_mut_vec().push(pre as u32);
    }

    pub(super) fn not_inner(&self) -> Vec<u32> {
        let mut v = Vec::with_capacity(self.num());
        
        let bitlen = self.bits_len() & 31;
        self.iter().for_each(|&a| {
            v.push(!a);
        });
        
        if bitlen > 0 {
            match v.last_mut() {
                Some(x) => {
                    *x = (*x) & ((1 << bitlen) - 1);
                },
                None => {},
            }
        }
        
        Self::trim_head_zero_(&mut v);
        v
    }

    #[inline]
    pub(super) fn nan() -> Nat {
        Nat::from(Vec::<u32>::new())
    }
    
    #[inline]
    pub(super) fn with_capacity(cap: usize) -> Nat {
        Nat {
            nat: Rc::new(Cell::new(Vec::with_capacity(cap))),
        }
    }
    
    pub(super) fn is_set_bit_(&self, idx: usize) -> bool {
        let (num, rem) = (idx >> 5, (idx & 31));
        match self.iter().nth(num) {
            Some(&x) => {
                (x & (1 << rem)) != 0
            },
            None => unreachable!(),
        }
    }
    
    /// check the bit is whether set to 1 in the `bit_idx`, 
    /// `None` if `bit_idx >= self.bits_len()`.
    pub fn is_set_bit(&self, bit_idx: usize) -> Option<bool> {
        if bit_idx >= self.bits_len() {None}
        else {Some(self.is_set_bit_(bit_idx))}
    }
    
    /// self ^ b
    pub fn pow(&self, b: Nat) -> Nat {
        if self.is_nan() || b.is_nan() {return Nat::nan();}
        
        let mut lhs = self.deep_clone();
        lhs.pow_inner(b);
        lhs
    }
    
    fn pow_inner(&mut self, b: Nat) {
        if &*self == &0u32 {
            if b == 0u32 {self.clear(); self.as_mut_vec().push(1);} 
            else {self.clear(); self.as_mut_vec().push(0);}
        }
        else if b.clone() == 0u32 {
            self.clear();
            self.as_mut_vec().push(1);
        }
        else {
            let b = if b.as_vec().as_ptr() == self.as_vec().as_ptr() {
                b.deep_clone()
            } else {
                b
            };
            
            let blen = b.bits_len();
            let mut pre = self.deep_clone();
            if !b.is_set_bit_(0) {
                self.clear();
                self.as_mut_vec().push(1u32);
            }
            (1..blen).for_each(|i| {
                pre.mul_inner(&pre.clone());
                if b.is_set_bit_(i) {
                    self.mul_inner(&pre);
                }
            });
        }
    }
    
    /// (self ^ b) mod n, self ^ b if n == 0
    /// 
    /// (a*b) mod c = ((a mod c) * (b mod c)) mod c
    pub fn pow_mod(&self, b: Nat, n: Nat) -> Nat {
        if self.is_nan() || b.is_nan() || n.is_nan() { return Nat::nan(); }
        
        let mut a = self.deep_clone();
        a.pow_mod_inner(b, n);
        a
    }
    
    fn pow_mod_inner(&mut self, b: Nat, n: Nat) {
        if n == 0u32 {
            self.pow_inner(b);
        } else if n == 1u32 {
            self.clear();
            self.as_mut_vec().push(0);
        } else {
            let n = if n.as_vec().as_ptr() == self.as_vec().as_ptr() {n.deep_clone()} else {n};
            let b = if b.as_vec().as_ptr() == self.as_vec().as_ptr() {b.deep_clone()} else {b};
            // 反复平方法
            let mut sm = self.deep_clone();
            self.clear();
            self.as_mut_vec().push(1);
            sm.rem_inner(&n);
            (0..b.bits_len()).rev().for_each(|i| {
                self.mul_inner(&self.clone());
                self.rem_inner(&n);
                if b.is_set_bit_(i) {
                    self.mul_inner(&sm);
                    self.rem_inner(&n);
                }
            });
        }
    }
    
    /// generate a random number that belong to the range of [0, self)
    pub fn random<Rng: IterSource<u32>>(&self, rng: &mut Rng) -> Nat {
        if self.is_nan() || self == &0u32 {
            return Nat::nan();
        }
        
        let bits_len = self.bits_len();
        let (num, rem) = (self.num(), bits_len & 31);
        let mask = if rem == 0 {u32::MAX} else {(1u32 << rem) - 1};
        
        let nat = Nat::with_capacity(num);
        
        let mut itr = rng.iter_mut();
        loop {
            let v = nat.as_mut_vec();
            v.clear();
            
            while v.len() < num {
                match itr.next() {
                    Some(x) => v.push(x),
                    None => itr.clear_error(),
                    // None => panic!("{}", itr.last_error().unwrap()),
                }
            }
            
            match v.last_mut() {
                Some(x) => *x &= mask,
                None => {},
            }
            
            if &nat < self {
                break;
            }
        }

        nat
    }

    /// compute the number of consecutive least significant zero bits of self
    pub fn trailling_zeros(&self) -> usize {
        let mut cnt = 0;
        for &ele in self.iter() {
            if ele == 0 {
                cnt += 32;
            } else {
                cnt += ele.trailing_zeros() as usize;
                break;
            }
        }
        cnt
    }

    /// 判断n是否是合数  
    fn miller_rabin_witness(&mut self, n: &Self) -> bool {
        let n_m1 = n.clone() - 1u32;
        let t = n_m1.trailling_zeros();
        let u = n_m1.clone() >> t;

        // let xi_m1 = self.pow_mod(u.clone(), n.clone());
        self.pow_mod_inner(u, n.clone());
        let xi_m1 = self;
        let mut xi = Nat::with_capacity(xi_m1.num());
        for _ in 1..=t {
            xi.as_mut_vec().clear();
            xi.as_mut_vec().extend_from_slice(xi_m1.as_slice());
            xi.mul_inner(&xi_m1);
            xi.rem_inner(n);

            if xi == 1u32 && *xi_m1 != 1u32 && *xi_m1 != n_m1 {
                return true;
            }
            xi_m1.as_mut_vec().clear();
            xi_m1.as_mut_vec().extend_from_slice(xi.as_slice());
        }

        *xi_m1 != 1u32
    }

    /// miller-rabin素数测试   
    /// 对于任意奇数n>2和正整数s, miller-rabin素数测试出错的概率至多为2^(-s)  
    /// 
    /// note: 内部调用函数, self是大于2的奇数, s>0  
    fn prime_validate_by_miller_rabin<Rng: IterSource<u32>>(&self, s: usize, rng: &mut Rng) -> bool {
        for _ in 0..s {
            let mut a = self.random(rng);
            if a.miller_rabin_witness(self) {
                return false;
            }
        }

        true
    }

    /// probablyPrimeLucas reports whether n passes the "almost extra strong" Lucas probable prime test,
    /// using Baillie-OEIS parameter selection. This corresponds to "AESLPSP" on Jacobsen's tables (link below).
    /// The combination of this test and a Miller-Rabin/Fermat test with base 2 gives a Baillie-PSW test.
    ///
    /// References:
    ///
    /// Baillie and Wagstaff, "Lucas Pseudoprimes", Mathematics of Computation 35(152),
    /// October 1980, pp. 1391-1417, especially page 1401.
    /// https://www.ams.org/journals/mcom/1980-35-152/S0025-5718-1980-0583518-6/S0025-5718-1980-0583518-6.pdf
    ///
    /// Grantham, "Frobenius Pseudoprimes", Mathematics of Computation 70(234),
    /// March 2000, pp. 873-891.
    /// https://www.ams.org/journals/mcom/2001-70-234/S0025-5718-00-01197-2/S0025-5718-00-01197-2.pdf
    ///
    /// Baillie, "Extra strong Lucas pseudoprimes", OEIS A217719, https://oeis.org/A217719.
    ///
    /// Jacobsen, "Pseudoprime Statistics, Tables, and Data", http://ntheory.org/pseudoprimes.html.
    ///
    /// Nicely, "The Baillie-PSW Primality Test", http://www.trnicely.net/misc/bpsw.html.
    /// (Note that Nicely's definition of the "extra strong" test gives the wrong Jacobi condition,
    /// as pointed out by Jacobsen.)
    ///
    /// Crandall and Pomerance, Prime Numbers: A Computational Perspective, 2nd ed.
    /// Springer, 2005.
    /// note: Miller-Rabin算法目前可以通过所有测试示例, 故lucas算法暂不实现
    fn prime_validate_by_lucas(&self) -> bool {
        if self.is_nan() || self == &1u32 {
            return false;
        }
        
        if (self.as_vec()[0] & 1) == 0 {
            return self == &2u32;
        }
        
        // Baillie-OEIS "method C" for choosing D, P, Q,
        // as in https://oeis.org/A217719/a217719.txt:
        // try increasing P ≥ 3 such that D = P² - 4 (so Q = 1)
        // until Jacobi(D, n) = -1.
        // The search is expected to succeed for non-square n after just a few trials.
        // After more than expected failures, check whether n is square
        // (which would cause Jacobi(D, n) = 1 for all D not dividing n).
        let mut p = 3;
        let mut t1 = Nat::nan();
        let (int_d, int_n) = (BigInt::from(1u32), BigInt::from(self.clone()));
        while p <= 10000 {
            int_d.get_nat().as_mut_vec()[0] = (p * p) - 4;
            let j = if let Some(x) = int_d.jacobi(&int_n) {x} else {return false};
            if j == -1 {
                break;
            }
            
            if j == 0 {
                // d = p²-4 = (p-2)(p+2).
                // If (d/n) == 0 then d shares a prime factor with n.
                // Since the loop proceeds in increasing p and starts with p-2==1,
                // the shared prime factor must be p+2.
                // If p+2 == n, then n is prime; otherwise p+2 is a proper factor of n.
                return self.as_vec().len() == 1 && self.as_vec()[0] == (p + 2);
            }
            
            if p == 40 {
                // We'll never find (d/n) = -1 if n is a square.
                // If n is a non-square we expect to find a d in just a few attempts on average.
                // After 40 attempts, take a moment to check if n is indeed a square.
                t1 = self.sqrt();
                t1 = t1.sqr();
                if &t1 == self {
                    return false;
                }
            }
            
            p += 1;
        }
        
        // Grantham definition of "extra strong Lucas pseudoprime", after Thm 2.3 on p. 876
        // (D, P, Q above have become Δ, b, 1):
        //
        // Let U_n = U_n(b, 1), V_n = V_n(b, 1), and Δ = b²-4.
        // An extra strong Lucas pseudoprime to base b is a composite n = 2^r s + Jacobi(Δ, n),
        // where s is odd and gcd(n, 2*Δ) = 1, such that either (i) U_s ≡ 0 mod n and V_s ≡ ±2 mod n,
        // or (ii) V_{2^t s} ≡ 0 mod n for some 0 ≤ t < r-1.
        //
        // We know gcd(n, Δ) = 1 or else we'd have found Jacobi(d, n) == 0 above.
        // We know gcd(n, 2) = 1 because n is odd.
        //
        // Arrange s = (n - Jacobi(Δ, n)) / 2^r = (n+1) / 2^r.
        let mut s = self.clone() + 1u32;
        let r = s.trailling_zeros();
        s.shr_inner(&r);
        let nm2 = self.clone() - 2u32;

        // We apply the "almost extra strong" test, which checks the above conditions
        // except for U_s ≡ 0 mod n, which allows us to avoid computing any U_k values.
        // Jacobsen points out that maybe we should just do the full extra strong test:
        // "It is also possible to recover U_n using Crandall and Pomerance equation 3.13:
        // U_n = D^-1 (2V_{n+1} - PV_n) allowing us to run the full extra-strong test
        // at the cost of a single modular inversion. This computation is easy and fast in GMP,
        // so we can get the full extra-strong test at essentially the same performance as the
        // almost extra strong test."

        // Compute Lucas sequence V_s(b, 1), where:
        //
        //	V(0) = 2
        //	V(1) = P
        //	V(k) = P V(k-1) - Q V(k-2).
        //
        // (Remember that due to method C above, P = b, Q = 1.)
        //
        // In general V(k) = α^k + β^k, where α and β are roots of x² - Px + Q.
        // Crandall and Pomerance (p.147) observe that for 0 ≤ j ≤ k,
        //
        //	V(j+k) = V(j)V(k) - V(k-j).
        //
        // So in particular, to quickly double the subscript:
        //
        //	V(2k) = V(k)² - 2
        //	V(2k+1) = V(k) V(k+1) - P
        //
        // We can therefore start with k=0 and build up to k=s in log₂(s) steps.
        let nat_p = Nat::from(p);
        let mut vk = Nat::from(2u32);
        let mut vk1 = Nat::from(p);
        for i in (0..=s.bits_len()).rev() {
            Self::mul_by_karatsuba(t1.as_mut_vec(), vk.as_slice(), vk1.as_slice());
            t1.add_inner(self);
            t1.sub_inner(&nat_p);
            
            match s.is_set_bit(i) {
                Some(true) => {
                    // k' = 2k+1
                    // V(k') = V(2k+1) = V(k) V(k+1) - P.
                    // Self::mul_by_karatsuba(t1.as_mut_vec(), vk.as_slice(), vk1.as_slice());
                    // t1.add_inner(self);
                    // t1.sub_inner(&nat_p);
                    vk = t1.clone() % self.clone();
                    // V(k'+1) = V(2k+2) = V(k+1)² - 2.
                    Self::sqr_v(t1.as_mut_vec(), vk1.as_slice());
                    t1.add_inner(&nm2);
                    vk1 = t1.clone() % self.clone();
                },
                _ => {
                    // k' = 2k
                    // V(k'+1) = V(2k+1) = V(k) V(k+1) - P.
                    // Self::mul_by_karatsuba(t1.as_mut_vec(), vk.as_slice(), vk1.as_slice());
                    // t1.add_inner(self);
                    // t1.sub_inner(&nat_p);
                    vk1 = t1.clone() % self.clone();
                    // V(k') = V(2k) = V(k)² - 2
                    Self::sqr_v(t1.as_mut_vec(), vk.as_slice());
                    t1.add_inner(&nm2);
                    vk = t1.clone() % self.clone();
                }
            }
        }

        // Now k=s, so vk = V(s). Check V(s) ≡ ±2 (mod n).
        if vk == 2u32 || vk == nm2 {
            // Check U(s) ≡ 0.
            // As suggested by Jacobsen, apply Crandall and Pomerance equation 3.13:
            //
            //	U(k) = D⁻¹ (2 V(k+1) - P V(k))
            //
            // Since we are checking for U(k) == 0 it suffices to check 2 V(k+1) == P V(k) mod n,
            // or P V(k) - 2 V(k+1) == 0 mod n.
            Self::mul_by_karatsuba(t1.as_mut_vec(), vk.as_slice(), nat_p.as_slice());
            t1 -= vk1 << 1;
            vk1 = t1.clone() % self.clone();
            if vk1 == 0u32 {
                return true;
            }
        }

        // Check V(2^t s) ≡ 0 mod n for some 0 ≤ t < r-1.
        for _ in 0..r.saturating_sub(1) {
            if vk == 0u32 {
                return true;
            }
            // Optimization: V(k) = 2 is a fixed point for V(k') = V(k)² - 2,
            // so if V(k) = 2, we can stop: we will never find a future V(k) == 0.
            if vk.as_vec().len() == 1 && vk.as_vec()[0] == 2 {
                return false;
            }
            // k' = 2k
            // V(k') = V(2k) = V(k)² - 2
            Self::sqr_v(t1.as_mut_vec(), vk.as_slice());
            t1 -= 2u32;
            vk = t1.clone() % self.clone();
        }
        return false;
    }

    /// probability prime test by the MillerRabin Pseudoprimes Algorithm and the Lucas Pseudoprimes Algorithms.   
    /// 
    /// n means the number of test rounds, for any odd number that great than 2 and positive integer n, the probability of error 
    /// in MillerRabinPrimeTest is at most $2^{-n}$.
    pub fn probably_prime_test<Rng: IterSource<u32>>(&self, n: usize, rng: &mut Rng) -> bool {
        if self.is_nan() || (self == &0u32) {
            return false;
        }

        const PRIME_BIT_MASK: u128 = 1<<2 | 1<<3 | 1<<5 | 1<<7 |
            1<<11 | 1<<13 | 1<<17 | 1<<19 | 1<<23 | 1<<29 | 1<<31 |
            1<<37 | 1<<41 | 1<<43 | 1<<47 | 1<<53 | 1<<59 | 1<<61 | 1<<67 |
            1<<71 | 1<<73 | 1<<79 | 1<<83 | 1<<89 | 1<<97 | 1<<101 |
            1<<103 | 1<<107 | 1<<109 | 1<< 113 | 1<<127;

        let x = self.as_vec()[0] as u128;
        // 小素数直接判断
        if (self.num() == 1) && (x < 128) {
            return ((1<<x) & PRIME_BIT_MASK) != 0;
        }

        // 偶数
        if x & 0x1 == 0 {
            return false;
        }

        const PRIMES_A: u32 = 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 37;
        const PRIMES_B: u32 = 29 * 31 * 41 * 43 * 47 * 53;
        let (ra, rb) = (self.clone() % PRIMES_A, self.clone() % PRIMES_B);
        if ra.clone()%3u32 == 0u32 || ra.clone()%5u32 == 0u32 || ra.clone()%7u32 == 0u32 || ra.clone()%11u32 == 0u32 || ra.clone()%13u32 == 0u32 
            || ra.clone()%17u32 == 0u32 || ra.clone()%19u32 == 0u32 || ra.clone()%23u32 == 0u32 || ra.clone()%37u32 == 0u32 ||
            rb.clone()%29u32 == 0u32 || rb.clone()%31u32 == 0u32 || rb.clone()%41u32 == 0u32 || rb.clone()%43u32 == 0u32 || rb.clone()%47u32 == 0u32 || rb.clone()%53u32 == 0u32 {
            return false
        }
        self.prime_validate_by_miller_rabin(n+1, rng) && self.prime_validate_by_lucas()
    }
    
    /// return $\lfloor \sqrt{self} \rfloor$ by the Newton's method  
    pub fn sqrt(&self) -> Nat {
        if self.is_nan() || self <= &1u32 {
            return self.deep_clone();
        }
        
        let mut z1 = Nat::from(1u32);
        z1 <<= (self.bits_len() + 1) >> 1;
        
        loop {
            let mut z2 = self.clone() / z1.clone();
            z2 += z1.clone();
            z2 >>= 1;
            
            if z2 >= z1 {
                return z1;
            }
            
            z1 = z2;
        }
    }
    
    /// Factored out for readability - do not use outside karatsuba.
    unsafe fn karatsuba_add(z: *mut u32, x: *const u32, n: usize) {
        let c = add_vv_inner(z, z, x, n);
        if c != 0 {
            add_vw_inner(z.add(n), z.add(n), c, n >> 1);
        }
    }

    unsafe fn karatsuba_sub(z: *mut u32, x: *const u32, n: usize) {
        let c = sub_vv_inner(z, z, x, n);
        if c != 0 {
            sub_vw_inner(z.add(n), z.add(n), c, n >> 1);
        }
    }

    unsafe fn basic_mul(z: *mut u32, x: *const u32, y: *const u32, xlen: usize, ylen: usize) {
        (0..(xlen + ylen)).for_each(|i| {z.add(i).write(0)});
        (0..ylen).for_each(|i| {
            let d = y.add(i).read();
            if d != 0 {
                z.add(xlen + i).write(add_mul_vvw_inner(z.add(i), x, d, xlen));
            }
        });
    }
    
    fn mul_add_ww(z: &mut Vec<u32>, x: &[u32], y: u32, r: u32) {
        let m = x.len();
        z.clear();
        if m == 0 || y == 0 {
            z.push(r);
            return;
        } else {
            z.resize(m + 1, 0);
            z[m] = mul_add_vww(&mut z[0..m], x, y, r);
            Self::trim_head_zero_(z);
        }
    }
    
    pub fn mul_karatsuba(&self, b: &Nat) -> Nat {
        let mut v = Vec::with_capacity(1);
        Self::mul_by_karatsuba(&mut v, self.as_slice(), b.as_slice());
        Nat::from(v)
    }
    
    fn mul_by_karatsuba(z: &mut Vec<u32>, x: &[u32], y: &[u32]) {
        let (m, n) = (x.len(), y.len());
        z.clear();
        if m < n {
            Self::mul_by_karatsuba(z, y, x);
            return;
        } else if m == 0 || n == 0 {
            return;
        } else if n == 1 {
            Self::mul_add_ww(z, x, y[0], 0);
            return;
        }
        
        if n < KARATSUBA_THRESHOLD {
            z.resize(m + n, 0);
            unsafe {
                Self::basic_mul(z.as_mut_ptr(), x.as_ptr(), y.as_ptr(), x.len(), y.len());
            }
            Self::trim_head_zero_(z);
            return;
        }
        
        // m >= n && n >= karatsubaThreshold && n >= 2

        // determine Karatsuba length k such that
        //
        //   x = xh*b + x0  (0 <= x0 < b)
        //   y = yh*b + y0  (0 <= y0 < b)
        //   b = 1<<(_W*k)  ("base" of digits xi, yi)
        let k = Self::karatsuba_len(n, KARATSUBA_THRESHOLD);
        let (x0, y0) = (&x[0..k], &y[0..k]);
        z.resize(std::cmp::max(6*k, m+n), 0);
        unsafe {
            Self::karatsuba(z.as_mut_ptr(), x0.as_ptr(), y0.as_ptr(), x0.len(), y0.len(), z.len());
        }
        
        z.truncate(m+n);
        z.iter_mut().skip(k<<1).for_each(|e| {*e = 0});// upper portion of z is garbage (and 2*k <= m+n since k <= n <= m)
        // If xh != 0 or yh != 0, add the missing terms to z. For
        //
        //   xh = xi*b^i + ... + x2*b^2 + x1*b (0 <= xi < b)
        //   yh =                         y1*b (0 <= y1 < b)
        //
        // the missing terms are
        //
        //   x0*y1*b and xi*y0*b^i, xi*y1*b^(i+1) for i > 0
        //
        // since all the yi for i > 1 are 0 by choice of k: If any of them
        // were > 0, then yh >= b^2 and thus y >= b^2. Then k' = k*2 would
        // be a larger valid threshold contradicting the assumption about k.
        //
        
        if k < n || m != n {
            let mut t = Vec::with_capacity(k * 3);
            let mut zero_count = 0;
            for &ele in x0.iter().rev() { if ele != 0 {break;} zero_count += 1};
            let x0 = &x0[..(x0.len() - zero_count)];
            let y1 = &y[k..];
            Self::mul_by_karatsuba(&mut t, x0, y1);
            unsafe {
                Self::add_at(z.as_mut_ptr(), t.as_ptr(), k, t.len(), z.len());
            }
            
            // add xi*y0<<i, xi*y1*b<<(i+k)
            zero_count = 0;
            for &ele in y0.iter().rev() { if ele != 0 {break;} zero_count += 1};
            let y0 = &y0[..(y0.len() - zero_count)];
            for i in (k..x.len()).step_by(k) {
                let xi = &x[i..];
                let xi = if xi.len() > k {
                    &xi[..k]
                } else {
                    xi
                };

                zero_count = 0;
                for &ele in xi.iter().rev() { if ele != 0 {break;} zero_count += 1};
                let xi = &xi[..(xi.len() - zero_count)];
                Self::mul_by_karatsuba(&mut t, xi, y0);
                unsafe {
                    Self::add_at(z.as_mut_ptr(), t.as_ptr(), i, t.len(), z.len());
                }
                Self::mul_by_karatsuba(&mut t, xi, y1);
                unsafe {
                    Self::add_at(z.as_mut_ptr(), t.as_ptr(), i + k, t.len(), z.len());
                }
            }
        }
        
        Self::trim_head_zero_(z);
    }

    /// karatsuba multiplies x and y and leaves the result in z.
    /// Both x and y must have the same length n and n must be a
    /// power of 2. The result vector z must have len(z) >= 6*n.
    /// The (non-normalized) result is placed in z[0 : 2*n].
    unsafe fn karatsuba(z: *mut u32, x: *const u32, y: *const u32, xlen: usize, ylen: usize, zlen: usize) {
        let n = ylen;

        // Switch to basic multiplication if numbers are odd or small.
        // (n is always even if karatsubaThreshold is even, but be
        // conservative)
        if (n & 1) != 0 || n < KARATSUBA_THRESHOLD || n < 2 {
            Self::basic_mul(z, x, y, xlen, ylen);
            return;
        }
        
        // n&1 == 0 && n >= karatsubaThreshold && n >= 2

        // Karatsuba multiplication is based on the observation that
        // for two numbers x and y with:
        //
        //   x = x1*b + x0
        //   y = y1*b + y0
        //
        // the product x*y can be obtained with 3 products z2, z1, z0
        // instead of 4:
        //
        //   x*y = x1*y1*b*b + (x1*y0 + x0*y1)*b + x0*y0
        //       =    z2*b*b +              z1*b +    z0
        //
        // with:
        //
        //   xd = x1 - x0
        //   yd = y0 - y1
        //
        //   z1 =      xd*yd                    + z2 + z0
        //      = (x1-x0)*(y0 - y1)             + z2 + z0
        //      = x1*y0 - x1*y1 - x0*y0 + x0*y1 + z2 + z0
        //      = x1*y0 -    z2 -    z0 + x0*y1 + z2 + z0
        //      = x1*y0                 + x0*y1

        // split x, y into "digits"
        let n2 = n >> 1;// n2 >= 1
        let (x1, x0, x0len, x1len) = (x.add(n2), x, n2, xlen - n2);// x = x1*b + y0
        let (y1, y0, y0len, y1len) = (y.add(n2), y, n2, ylen - n2);// y = y1*b + y0

        // z is used for the result and temporary storage:
        //
        //   6*n     5*n     4*n     3*n     2*n     1*n     0*n
        // z = [z2 copy|z0 copy| xd*yd | yd:xd | x1*y1 | x0*y0 ]
        //
        // For each recursive call of karatsuba, an unused slice of
        // z is passed in that has (at least) half the length of the
        // caller's z.

        // compute z0 and z2 with the result "in place" in z
        Self::karatsuba(z, x0, y0, x0len, y0len, zlen);     // z0 = x0*y0
        Self::karatsuba(z.add(n), x1, y1, x1len, y1len, zlen.saturating_sub(n)); // z2 = x1*y1

        // compute xd (or the negative value if underflow occurs)
        let mut s = 1;// sign of product xd*yd
        let (xd, xdlen) = (z.add(n << 1), n2);
        let tmp = std::cmp::min(xdlen, x1len);
        if sub_vv_inner(xd, x1, x0, tmp) != 0 {
            s = -s;
            sub_vv_inner(xd, x0, x1, tmp);
        }

        // compute yd (or the negative value if underflow occurs)
        let (yd, ydlen) = (z.add((n<<1) + n2), n.saturating_sub(n2));
        let tmp = std::cmp::min(ydlen, std::cmp::min(y0len, y1len));
        if sub_vv_inner(yd, y0, y1, tmp) != 0 {
            s = -s;
            sub_vv_inner(yd, y1, y0, tmp);
        }

        // p = (x1-x0)*(y0-y1) == x1*y0 - x1*y1 - x0*y0 + x0*y1 for s > 0
        // p = (x0-x1)*(y0-y1) == x0*y0 - x0*y1 - x1*y0 + x1*y1 for s < 0
        let (p, plen) = (z.add((n<<1)+n), zlen - ((n<<1)+n));
        Self::karatsuba(p, xd, yd, xdlen, ydlen, plen);

        // save original z2:z0
        // (ok to use upper half of z since we're done recursing)
        let (r, rlen) = (z.add(n<<2), zlen - (n<<2));
        let tmp = std::cmp::min(n<<1, rlen);
        for i in 0..tmp {
            r.add(i).write(z.add(i).read());
        }

        // add up all partial products
        //
        //   2*n     n     0
        // z = [ z2  | z0  ]
        //   +    [ z0  ]
        //   +    [ z2  ]
        //   +    [  p  ]
        //
        Self::karatsuba_add(z.add(n2), r, n);
        Self::karatsuba_add(z.add(n2), r.add(n), n);
        if s > 0 {
            Self::karatsuba_add(z.add(n2), p, n);
        } else {
            Self::karatsuba_sub(z.add(n2), p, n);
        }
    }
    
    /// karatsubaLen computes an approximation to the maximum k <= n such that
    /// k = p<<i for a number p <= threshold and an i >= 0. Thus, the
    /// result is the largest number that can be divided repeatedly by 2 before
    /// becoming about the value of threshold.
    fn karatsuba_len(mut n: usize, threshold: usize) -> usize {
        let mut i = 0;
        while n > threshold {
            n >>= 1;
            i += 1;
        }
        
        n << i
    }
    
    unsafe fn basic_sqr(z: *mut u32, x: *const u32, xlen: usize, zlen: usize) {
        let mut t = Vec::with_capacity(xlen << 1);
        t.resize(xlen << 1, 0);
        let (z1, z0) = mul_ww(x.read(), x.read());
        z.write(z0);
        z.add(1).write(z1);
        
        let t_ptr = t.as_mut_ptr();
        for i in 1..xlen {
            let d = x.add(i).read();
            let (z1, z0) = mul_ww(d, d);
            // z collects the squares x[i] * x[i]
            let idx = i << 1;
            z.add(idx).write(z0);
            z.add(idx + 1).write(z1);
            // t collects the products x[i] * x[j] where j < i
            let z0 = add_mul_vvw_inner(t.as_mut_ptr().add(i), x, d, i);
            t_ptr.add(idx).write(z0);
        }
        
        let tmp = (xlen << 1) - 1;
        t[tmp] = shl_vu_inner(t.as_mut_ptr().add(1), t.as_mut_ptr().add(1), 1, tmp-1);
        add_vv_inner(z, z, t.as_ptr(), std::cmp::min(zlen, xlen << 1));
    }
    
    unsafe fn karatsuba_sqr(z: *mut u32, x: *const u32, xlen: usize, zlen: usize) {
        let n = xlen;
        if (n & 1) != 0 || n < KARATSUBA_THRESHOLD || n < 2 {
            Self::basic_sqr(z, x, xlen, zlen);
            return;
        }
        
        let n2 = n >> 1;
        let (x1, x0, x1len, x0len) = (x.add(n2), x, n - n2, n2);
        Self::karatsuba_sqr(z, x0, x0len, zlen);
        Self::karatsuba_sqr(z.add(n), x1, x1len, zlen - n);
        
        // s = sign(xd*yd) == -1 for xd != 0; s == 1 for xd == 0
        let (xd, xdlen) = (z.add(n<<1), n2);
        let tmp = std::cmp::min(xdlen, std::cmp::min(x0len, x1len));
        if sub_vv_inner(xd, x1, x0, tmp) != 0 {
            sub_vv_inner(xd, x0, x1, tmp);
        }
        
        let (p, plen) = (z.add((n<<1) + n), zlen - ((n<<1) + n));
        Self::karatsuba_sqr(p, xd, xdlen, plen);
        let (r, rlen) = (z.add(n<<2), zlen - (n<<2));
        let tmp = std::cmp::min(rlen, n<<1);
        (0..tmp).for_each(|i| {
            r.add(i).write(z.add(i).read());
        });
        
        Self::karatsuba_add(z.add(n2), r, n);
        Self::karatsuba_add(z.add(n2), r.add(n), n);
        Self::karatsuba_sub(z.add(n2), p, n); // s == -1 for p != 0; s == 1 for p == 0
    }
    
    // addAt implements z += x<<(_W*i); z must be long enough.
    unsafe fn add_at(z: *mut u32, x: *const u32, i: usize, xlen: usize, zlen: usize) {
        if xlen > 0 {
            let c = add_vv_inner(z.add(i), z.add(i), x, xlen);
            if c != 0 {
                let j = i + xlen;
                if j < zlen {
                    add_vw_inner(z.add(j), z.add(j), c, zlen - j);
                }
            }
        }
    }
    
    /// result = self * self
    pub fn sqr(&self) -> Nat {
        let mut z = Vec::new();
        Self::sqr_v(&mut z, self.as_slice());
        Nat::from(z)
    }
    
    /// z = x * x
    pub(super) fn sqr_v(z: &mut Vec<u32>, x: &[u32]) {
        z.clear();
        if x.len() == 0 {
            return;
        } else if x.len() == 1 {
            let d = x[0];
            let (z1, z0) = mul_ww(d, d);
            z.push(z0);
            z.push(z1);
            Self::trim_head_zero_(z);
            return;
        }
        
        if x.len() < BASIC_SQRT_HRESHOLD {
            z.resize(x.len() << 1, 0);
            unsafe {
                Self::basic_mul(z.as_mut_ptr(), x.as_ptr(), x.as_ptr(), x.len(), x.len());
            }
            Self::trim_head_zero_(z);
            return;
        }
        
        if x.len() < KARATSUBA_SQRT_HRESHOLD {
            z.resize(x.len() << 1, 0);
            unsafe {
                Self::basic_sqr(z.as_mut_ptr(), x.as_ptr(), x.len(), z.len());
            }
            Self::trim_head_zero_(z);
            return;
        }

        // Use Karatsuba multiplication optimized for x == y.
        // The algorithm and layout of z are the same as for mul.

        // z = (x1*b + x0)^2 = x1^2*b^2 + 2*x1*x0*b + x0^2
        let k = Self::karatsuba_len(x.len(), KARATSUBA_SQRT_HRESHOLD);
        let x0 = &x[0..k];
        z.resize(std::cmp::max(k*6, x.len() * 2), 0u32);
        unsafe {
            Self::karatsuba_sqr(z.as_mut_ptr(), x0.as_ptr(), x0.len(), z.len());
        }
        
        z.truncate(x.len() << 1);
        z.iter_mut().skip(k<<1).for_each(|e| {*e = 0});
        
        if k < x.len() {
            let mut t = Vec::with_capacity(k << 1);
            let mut zero_count = 0;
            for &ele in x0.iter().rev() {if ele != 0 {break;} zero_count += 1;}
            let x0 = &x0[..(x0.len() - zero_count)];
            let x1 = &x[k..];
            Self::mul_by_karatsuba(&mut t, x0, x1);
            unsafe {
                Self::add_at(z.as_mut_ptr(), t.as_ptr(), k, t.len(), z.len());
                Self::add_at(z.as_mut_ptr(), t.as_ptr(), k, t.len(), z.len());// z = 2*x1*x0*b + x0^2
            }
            Self::sqr_v(&mut t, x1);
            unsafe {
                Self::add_at(z.as_mut_ptr(), t.as_ptr(), k << 1, t.len(), z.len());
            }
        }
        
        Self::trim_head_zero_(z);
    }
    
    /// this code convert from golang  
    /// montgomery computes z mod m = x*y*2**(-n*_W) mod m,
    /// assuming k = -1/m mod 2**_W.  
    /// z is used for storing the result which is returned;  
    /// See Gueron, "Efficient Software Implementations of Modular Exponentiation".  
    /// https://eprint.iacr.org/2011/239.pdf  
    /// In the terminology of that paper, this is an "Almost Montgomery Multiplication":  
    /// x and y are required to satisfy 0 <= z < 2**(n*_W) and then the result  
    /// z is guaranteed to satisfy 0 <= z < 2**(n*_W), but it may not be < m.  
    fn montgomery(z: &mut Vec<u32>, x: &Vec<u32>, y: &Vec<u32>, m: &Vec<u32>, k: u32, n: usize) {
        if x.len() != n || y.len() != n || m.len() != n {
            panic!("mismatched montgomery number lengths");
        }
        
        z.clear();
        z.resize(n<<1, 0);
        let mut c = 0u32;
        
        for i in 0..n {
            let d = y[i];
            let c2 = add_mul_vvw(&mut z[i..(n+i)], x, d);
            let t = z[i].wrapping_mul(k);
            let c3 = add_mul_vvw(&mut z[i..(n+i)], m, t);
            let cx = c.wrapping_add(c2);
            let cy = cx.wrapping_add(c3);
            z[n + i] = cy;
            c = if cx < c2 || cy < c3 {1} else {0};
        }
        
        if c != 0 {
            unsafe {
                let z0 = z.as_mut_ptr();
                let z1 = z0.add(n);
                sub_vv_inner(z0, z1, m.as_ptr(), n);
            }
        } else {
            for i in 0..n {
                z[i] = z[n+i];
            }
        }
        z.truncate(n);
    }
    
    /// $z = x^y \mod m$
    fn exp_montogomery(z: &mut Nat, x: &Nat, y: &Nat, m: &Nat) {
        let num_words = m.as_vec().len();
        let x = if x.as_vec().len() > num_words {
            x.clone() % m.clone()
        } else {
            x.deep_clone()
        };
        if x.as_vec().len() < num_words {
            x.as_mut_vec().resize(num_words, 0);
        }
        // Ideally the precomputations would be performed outside, and reused
        // k0 = -m**-1 mod 2**_W. Algorithm from: Dumas, J.G. "On Newton–Raphson
        // Iteration for Multiplicative Inverses Modulo Prime Powers".
        let (mut i, mut k0, mut t) = (1, 2u32.wrapping_sub(m.as_vec()[0]), m.as_vec()[0].wrapping_sub(1));
        while i < 32 {
            t = t.wrapping_mul(t);
            k0 = k0.wrapping_mul(t.wrapping_add(1));
            i <<= 1;
        }
        k0 = k0.wrapping_neg();
        
        // RR = 2**(2*_W*len(m)) mod m
        let mut rr = Nat::from(1u32);
        rr <<= num_words << 6;
        rr %= m.clone();
        if rr.as_vec().len() < num_words {
            rr.as_mut_vec().resize(num_words, 0);
        }
        let one = Nat::from(1u32);
        one.as_mut_vec().resize(num_words, 0);
        
        let n:usize = 4;
        
        let powers = [
            Nat::from(0u32), Nat::from(0u32),Nat::from(0u32),Nat::from(0u32),
            Nat::from(0u32), Nat::from(0u32),Nat::from(0u32),Nat::from(0u32),
            Nat::from(0u32), Nat::from(0u32),Nat::from(0u32),Nat::from(0u32),
            Nat::from(0u32), Nat::from(0u32),Nat::from(0u32),Nat::from(0u32),
        ];
        Self::montgomery(powers[0].as_mut_vec(), one.as_vec(), rr.as_vec(), m.as_vec(), k0, num_words);
        Self::montgomery(powers[1].as_mut_vec(), x.as_vec(), rr.as_vec(), m.as_vec(), k0, num_words);
        (2..(1 << n)).for_each(|i| {
            Self::montgomery(powers[i].as_mut_vec(), powers[i-1].as_vec(), powers[1].as_vec(), m.as_vec(), k0, num_words);
        });

        // initialize z = 1 (Montgomery 1)
        let zz = &mut rr;
        z.clear();
        z.as_mut_vec().extend(powers[0].as_vec().iter());
        zz.clear();
        zz.as_mut_vec().resize(num_words, 0);
        
        let (mut tmpz, mut tmpzz, mut is_switch) = (z, zz, false);
        // same windowed exponent, but with Montgomery multiplications
        for (i, &ye) in y.iter().enumerate().rev() {
            let mut yi = ye;
            for j in (0..32).step_by(n) {
                if i != (y.as_vec().len() - 1) || j != 0 {
                    Self::montgomery(tmpzz.as_mut_vec(), tmpz.as_vec(), tmpz.as_vec(), m.as_vec(), k0, num_words);
                    Self::montgomery(tmpz.as_mut_vec(), tmpzz.as_vec(), tmpzz.as_vec(), m.as_vec(), k0, num_words);
                    Self::montgomery(tmpzz.as_mut_vec(), tmpz.as_vec(), tmpz.as_vec(), m.as_vec(), k0, num_words);
                    Self::montgomery(tmpz.as_mut_vec(), tmpzz.as_vec(), tmpzz.as_vec(), m.as_vec(), k0, num_words);
                }
                
                Self::montgomery(tmpzz.as_mut_vec(), tmpz.as_vec(), powers[((yi as usize) >> (32 - n))].as_vec(), m.as_vec(), k0, num_words);
                let tmp = tmpz;
                tmpz = tmpzz;
                tmpzz = tmp;
                is_switch = !is_switch;
                yi <<= n;
            }
        }
        
        // convert to regular number
        Self::montgomery(tmpzz.as_mut_vec(), tmpz.as_vec(), one.as_vec(), m.as_vec(), k0, num_words);
        if *tmpzz >= *m {
            *tmpzz -= m.clone();
            if *tmpzz >= *m {
                *tmpzz %= m.clone();
            }
        }
        tmpzz.trim_head_zero();
        
        if !is_switch {
            tmpz.clear();
            tmpz.as_mut_vec().extend(tmpzz.iter());
        }
    }
    
    fn exp_windowed(o: &mut Nat, x: &Nat, y: &Nat, m: &Nat) {
        let n = 4;

        let powers = [
            Nat::from(1u32), x.deep_clone(), Nat::from(0u32),Nat::from(0u32),
            Nat::from(0u32), Nat::from(0u32),Nat::from(0u32),Nat::from(0u32),
            Nat::from(0u32), Nat::from(0u32),Nat::from(0u32),Nat::from(0u32),
            Nat::from(0u32), Nat::from(0u32),Nat::from(0u32),Nat::from(0u32),
        ];
        
        for i in (2..(1<<4)).step_by(2) {
            let (p2, p, p1) = (&powers[i>>1], &powers[i], &powers[i+1]);
            Self::sqr_v(p.as_mut_vec(), p2.as_slice());
            let r = p.clone() % m.clone();
            p.as_mut_vec().clear();
            p.as_mut_vec().extend(r.iter());
            Self::mul_by_karatsuba(p1.as_mut_vec(), p.as_slice(), x.as_slice());
            let r = p1.clone() % m.clone();
            p1.as_mut_vec().clear();
            p1.as_mut_vec().extend(r.iter());
        }
        
        let mut z = Nat::from(1u32);
        let mut buf = Nat::with_capacity(32);
        let (mut z, mut zz) = (&mut z, &mut buf);
        
        let ylen = y.as_vec().len();
        for (i, &ele) in y.iter().enumerate().rev() {
            let mut yi = ele;
            for j in (0..32).step_by(n) {
                if i != (ylen - 1) || j != 0 {
                    Self::sqr_v(zz.as_mut_vec(), z.as_slice());
                    let tmp = z; z = zz; zz = tmp;
                    *z %= m.clone();
                    
                    Self::sqr_v(zz.as_mut_vec(), z.as_slice());
                    let tmp = z; z = zz; zz = tmp;
                    *z %= m.clone();

                    Self::sqr_v(zz.as_mut_vec(), z.as_slice());
                    let tmp = z; z = zz; zz = tmp;
                    *z %= m.clone();

                    Self::sqr_v(zz.as_mut_vec(), z.as_slice());
                    let tmp = z; z = zz; zz = tmp;
                    *z %= m.clone();
                }
                
                Self::mul_by_karatsuba(zz.as_mut_vec(), z.as_slice(), powers[(yi as usize) >> (32 - n)].as_slice());
                let tmp = z; z = zz; zz = tmp;
                *z %= m.clone();
                yi <<= n;
            }
        }

        z.trim_head_zero();
        o.clear();
        o.as_mut_vec().extend(z.iter());
    }
    
    /// $self^b \mod n$ same as `pow_mod` 
    pub fn exp(&self, b: &Nat, n: &Nat) -> Nat {
        if self.is_nan() || b.is_nan() || n.is_nan() { return Nat::nan(); }
        
        if n.as_vec().len() == 1 && n.as_vec()[0] == 1 {
            return Nat::from(0u32);
        }
        
        if b.as_vec().len() == 1 {
            if b.as_vec()[0] == 0 {
                return Nat::from(1u32);
            } else if b.as_vec()[0] == 1 {
                if n.as_vec().len() == 1 && n.as_vec()[0] == 0 {
                    return self.deep_clone();
                } else {
                    return self.clone() % n.clone();
                }
            }
        }
        
        let mut z = Nat::with_capacity(n.as_vec().len());
        z.as_mut_vec().extend(self.iter());
        // If the base is non-trivial and the exponent is large, we use
        // 4-bit, windowed exponentiation. This involves precomputing 14 values
        // (x^2...x^15) but then reduces the number of multiply-reduces by a
        // third. Even for a 32-bit exponent, this reduces the number of
        // operations. Uses Montgomery method for odd moduli.
        if (self.as_vec().len() > 1 || self.as_vec()[0] > 1) && b.as_vec().len() > 1 && (n.as_vec().len() > 1 || n.as_vec()[0] > 0) {
            if (n.as_vec()[0] & 1) == 1 {
                Self::exp_montogomery(&mut z, self, b, n);
            } else {
                Self::exp_windowed(&mut z, self, b, n);
            }
            return z;
        }

        let mut v = *b.as_vec().last().unwrap();
        let shift = v.leading_zeros() + 1;
        v <<= shift;
        let mask = 1u32 << (32 - 1);
        let w = 32 - shift;
        
        let mut zz = Nat::with_capacity(32);
        let (mut z, mut zz) = (&mut z, &mut zz);
        for _ in 0..w {
            Self::sqr_v(zz.as_mut_vec(), z.as_slice());
            let tmp = z; z = zz; zz = tmp;
            if (v & mask) != 0 {
                Self::mul_by_karatsuba(zz.as_mut_vec(), z.as_slice(), self.as_slice());
                let tmp = z; z = zz; zz = tmp;
            }
            
            if !(n.as_vec().len() == 1 && n.as_vec()[0] == 0) {
                let r = z.clone() % n.clone();
                z.as_mut_vec().clear();
                z.as_mut_vec().extend(r.iter());
            }
            
            v <<= 1;
        }
        
        for &be in b.iter().rev().skip(1) {
            let mut v = be;
            for _ in 0..32 {
                Self::sqr_v(zz.as_mut_vec(), z.as_slice());
                let tmp = z; z = zz; zz = tmp;

                if (v & mask) != 0 {
                    Self::mul_by_karatsuba(zz.as_mut_vec(), z.as_slice(), self.as_slice());
                    let tmp = z; z = zz; zz = tmp;
                }

                if !(n.as_vec().len() == 1 && n.as_vec()[0] == 0) {
                    let r = z.clone() % n.clone();
                    z.as_mut_vec().clear();
                    z.as_mut_vec().extend(r.iter());
                }

                v <<= 1;
            }
        }
        
        z.trim_head_zero();
        z.deep_clone()
    }
    
    /// computes the product of all the unsigned integers in the
    /// range [a, b] inclusively. If a > b (empty range), the result is 1.
    pub(super) fn mul_range(a: u64, b: u64) -> Nat {
        if a == 0 {
            Nat::from(0u32)
        } else if a > b {
            Nat::from(1u32)
        } else if a == b {
            Nat::from(a)
        } else {
            let mut res = Nat::from(b);
            let mut tmp_high = Nat::with_capacity(2);
            let tmp_low = Nat::with_capacity(2);
            for e in a..b {
                let (high, lower) = ((e >> 32) as u32, (e & (u32::MAX) as u64) as u32);
                Self::mul_add_ww(tmp_high.as_mut_vec(), res.as_slice(), high, 0);
                Self::mul_add_ww(tmp_low.as_mut_vec(), res.as_slice(), lower, 0);
                tmp_high.shl_inner(&32);
                
                let len = std::cmp::max(tmp_high.as_vec().len(), tmp_low.as_vec().len());
                tmp_high.as_mut_vec().resize(len, 0);
                tmp_low.as_mut_vec().resize(len, 0);
                res.as_mut_vec().resize(len, 0);
                let c = add_vv(res.as_mut_slice(), tmp_high.as_slice(), tmp_low.as_slice());
                res.as_mut_vec().push(c);
                res.trim_head_zero();
            }
            
            res
        }
    }
    
    /// the `i`'th bit of the `self` is set to the 1 if `is_set` is true, otherwise 0.  
    /// the bits len of the `self` will grow to the `i+1` if `i >= self.bits_len()`
    pub(super) fn set_bits(&mut self, i: usize, is_set: bool) {
        let (j, m) = (i / 32, 1 << (i % 32));
        let n = self.as_vec().len();
        if is_set {
            if j >= n {
                self.as_mut_vec().resize(j + 1, 0);
            }
            
            self.as_mut_vec()[j] |= m;
        } else {
            if j < n {
                self.as_mut_vec()[j] &= !m;
            }
        }
    }

    /// sticky returns 1 if there's a 1 bit within the
    /// i least significant bits, otherwise it returns 0.
    pub(super) fn sticky(&self, bits_num: usize) -> usize {
        if self.is_nan() {return 0;}
        let j = bits_num >> 5;
        if j >= self.as_vec().len() {
            if self == &0u32 {
                0
            } else {
                1
            }
        } else {
            for &x in self.iter().take(j) {
                if x != 0 {
                    return 1;
                }
            }
            
            let rom = bits_num & 31;
            if rom > 0 && (self.as_vec()[j] << (32 - rom)) != 0 {
                1
            } else {
                0
            }
        }
    }
} // Nat

impl Default for Nat {
    fn default() -> Self {
        Nat {nat: Rc::new(Cell::new(Vec::new()))}
    }
}

nat_from_basic!(u8, u16, u32, u64, u128, usize);

impl From<Vec<u32>> for Nat {
    /// lower dword first, byte word following the system
    fn from(x: Vec<u32>) -> Self {
        let mut x = x;
        Self::trim_head_zero_(&mut x);
        
        Nat {nat: Rc::new(Cell::new(x))}
    }
}

impl From<&Vec<u32>> for Nat {
    /// lower dword first, byte word following the system
    fn from(x: &Vec<u32>) -> Self {
        Self::from(x.clone())
    }
}

impl From<&[u32]> for Nat {
    /// lower dword first, byte word following the system
    fn from(x: &[u32]) -> Self {
        Self::from(x.to_vec())
    }
}

impl From<&[u8]> for Nat {
    /// little endian
    fn from(x: &[u8]) -> Self {
        const MASK: usize = 3;
        let mut v = Vec::with_capacity((x.len() + MASK) >> 2);
        let mut tmp = 0;
        x.iter().enumerate().for_each(|(i, &ele)| {
            tmp += (ele as u32) << ((i & MASK) << 3);
            if (i & MASK) == 3 {
                v.push(tmp);
                tmp = 0;
            }
        });
        
        if tmp > 0 {v.push(tmp);}
        else { if !x.is_empty() {v.push(tmp);}}
        
        Self::trim_head_zero_(&mut v);
        Nat {nat: Rc::new(Cell::new(v))}
    }
}

impl From<Vec<u8>> for Nat {
    /// little endian
    fn from(x: Vec<u8>) -> Self {
        Nat::from(x.as_slice())
    }
}

impl From<&Vec<u8>> for Nat {
    fn from(x: &Vec<u8>) -> Self {
        Nat::from(x.as_slice())
    }
}

impl FromStr for Nat {
    type Err = NatError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();
        let (i, base) = Self::check_base(s)?;
        let s = &s[i..];
        
        match base {
            2 => Self::from_bin_str(s),
            8 => Self::from_oct_str(s),
            10 => Self::from_dec_str(s),
            16 => Self::from_hex_str(s),
            _ => unreachable!(),
        }
    }
}

nat_fmt!((Binary, "{:032b}", "0b"), (LowerHex, "{:08x}", "0x"), (Debug, "{:08x}", "0x"), (UpperHex, "{:08X}", "0x"));

impl Octal for Nat {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.is_nan() {
            return write!(f, "{}", "NaN");
        }

        let mut nat_str = String::with_capacity(self.num() * 11);

        let mut pre = 0;
        for (i, &ele) in self.iter().enumerate() {
            let tmp = match i % 3 {
                0 => {
                    (ele, (ele >> 30) as u8)
                },
                1 => {
                    let val = ((((ele & 0x1) << 2) as u8) | pre) + b'0';
                    nat_str.push(val as char);
                    (ele >> 1, (ele >> 31) as u8)
                },
                _ => {
                    let val = ((((ele & 0x3) << 1) as u8) | pre) + b'0';
                    nat_str.push(val as char);
                    (ele >> 2, 0)
                },
            };
            
            pre = tmp.1;
            for idx in 0..10u32 {
                let val = (((tmp.0 >> (idx * 3)) & 0x7u32) as u8) + b'0';
                nat_str.push(val as char);
            }
        }

        if pre > 0 { nat_str.push((pre + b'0') as char);}
        let nat_str: String = nat_str.chars().rev().collect();
        let (nat, prefix) = (nat_str.trim_start_matches('0'), if f.alternate() {"0o"} else {""});
        
        if nat.is_empty() && self.num() > 0 {
            write!(f, "{}{}", prefix, 0)
        } else {
            write!(f, "{}{}", prefix, nat)
        }
    }
}

impl Display for Nat {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.is_nan() {
            return write!(f, "{}", "NaN");
        }
        let (zero, ten) = (Nat::from(0u8), Nat::from(10u8));
        let mut nat_str = Vec::with_capacity(self.bits_len() >> 3);
        
        let mut nat = self.deep_clone();
        while nat != zero {
            let rem = nat.clone() % ten.clone();
            nat /= ten.clone();
            let val = rem.as_vec().first().unwrap();
            nat_str.push(format!("{}", val));
        }
        if nat_str.is_empty() {
            write!(f, "{}", 0)
        } else {
            nat_str.reverse();
            write!(f, "{}", nat_str.join(""))
        }
    }
}

impl PartialEq for Nat {
    fn eq(&self, other: &Self) -> bool {
        if self.is_nan() {
            false
        } else {
            self.as_vec() == other.as_vec()
        }
    }
}

nat_eq_basic!(u8, u16, u32, u64, u128, usize);

impl PartialOrd for Nat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.is_nan() || other.is_nan() {
            return None;
        }
        
        Some(self.partial_cmp_inner(other))
    }
}

nat_ord_basic!(u8, u16, u32, u64, u128, usize);

nat_arith_ops1!(
    (Nat, Mul, MulAssign, mul, mul_assign, mul_inner, |rhs: &Nat| {rhs.is_nan()}),
    (u32, Mul, MulAssign, mul, mul_assign, mul_inner_basic, |_rhs: &u32| {false}),
    (u32, Rem, RemAssign, rem, rem_assign, rem_inner_basic, |_rhs: &u32| {false}),
    (u32, Div, DivAssign, div, div_assign, div_inner_basic, |_rhs: &u32| {false}),
    (Nat, BitXor, BitXorAssign, bitxor, bitxor_assign, bitxor_inner, |rhs: &Nat| {rhs.is_nan()}),
    (Nat, BitOr, BitOrAssign, bitor, bitor_assign, bitor_inner, |rhs: &Nat| {rhs.is_nan()}),
    (Nat, BitAnd, BitAndAssign, bitand, bitand_assign, bitand_inner, |rhs: &Nat| {rhs.is_nan()}),
    (Nat, Rem, RemAssign, rem, rem_assign, rem_inner, |rhs: &Nat| {rhs.is_nan()}),
    (Nat, Div, DivAssign, div, div_assign, div_inner, |rhs: &Nat| {rhs.is_nan()}),
    (usize, Shr, ShrAssign, shr, shr_assign, shr_inner, |_rhs: &usize| {false}),
    (usize, Shl, ShlAssign, shl, shl_assign, shl_inner, |_rhs: &usize| {false}),
    (Nat, Sub, SubAssign, sub, sub_assign, sub_inner, |rhs: &Nat| {rhs.is_nan()}),
    (u32, Sub, SubAssign, sub, sub_assign, sub_inner_basic, |_rhs: &u32| {false}),
    (u32, Add, AddAssign, add, add_assign, add_inner_basic, |_rhs: &u32| {false}),
    (Nat, Add, AddAssign, add, add_assign, add_inner, |rhs: &Nat| {rhs.is_nan()})
);

impl Not for Nat {
    type Output = Nat;

    fn not(self) -> Self::Output {
        if self.is_nan() {
            Nat::default()
        } else {
            Nat::from(self.not_inner())
        }
    }
}

