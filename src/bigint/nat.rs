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
    
    /// little endian
    pub fn to_le_bytes(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(self.num() << 2);
        self.iter().for_each(|&x| {v.extend_from_slice(x.to_le_bytes().as_ref());});
        let mut i = 0;
        for &ele in v.iter().rev() {
            if ele != 0 {
                break;
            }
            i += 1;
        }
        
        if v.len() > 0 && i == v.len() {
            v.truncate(v.len() + 1 - i);
        } else {
            v.truncate(v.len() - i);
        }
        v
    }
    
    /// big endian
    pub fn to_be_bytes(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(self.num() << 2);
        let mut itr = self.iter().rev();
        match itr.next() {
            Some(&x) => {
                if (x == 0) && (self.num() == 1) {
                    v.push(0);
                } else {
                    let n = (x.leading_zeros() as usize) >> 3;
                    let tmp = x.to_be_bytes();
                    v.extend_from_slice(&tmp[n..]);
                }
            },
            None => {},
        }
        itr.for_each(|&x| {v.extend_from_slice(x.to_be_bytes().as_ref());});
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
        // Baillie-OEIS "method C" for choosing D, P, Q,
        // as in https://oeis.org/A217719/a217719.txt:
        // try increasing P ≥ 3 such that D = P² - 4 (so Q = 1)
        // until Jacobi(D, n) = -1.
        // The search is expected to succeed for non-square n after just a few trials.
        // After more than expected failures, check whether n is square
        // (which would cause Jacobi(D, n) = 1 for all D not dividing n).
        true
    }

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
}

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

