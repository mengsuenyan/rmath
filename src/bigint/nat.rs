/// 自然数

use std::rc::Rc;
use std::str::FromStr;
use crate::bigint::nat_err::NatError;
use crate::parse_err::ParseErrKind::{BeginWithIllegalChar, IllegalCharEncounter};
use std::fmt::{Debug, Binary, LowerHex, UpperHex, Octal, Formatter};
use std::cell::Cell;
use std::cmp::Ordering;
use std::ops::{Add, AddAssign, SubAssign, Sub, ShrAssign, Shr, Shl, ShlAssign, 
    Div, DivAssign, Mul, MulAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign,
    BitXor, BitXorAssign, Not, Rem, RemAssign};

#[cfg(test)]
mod tests;

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
    
    pub(super) fn to_vec(&self) -> Vec<u32> {
        self.as_vec().clone()
    }
    
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
        for &ele in v.iter() {
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
    
    pub(super) fn min_max_by_len<'a>(x: &'a[u32], y: &'a[u32]) -> (&'a[u32], &'a[u32]) {
        if x.len() < y.len() {(x, y)} else {(y, x)}
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
                                    if x.is_ascii_digit() {
                                        Ok((i+1,8))
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
        
        Err(NatError::new(BeginWithIllegalChar, "all char is +"))
    }
    
    fn from_dec_str(s: &str) -> Result<Self, NatError> {
        let mut v = Vec::with_capacity(s.len() / 10);
        const ZERO: u32 = '0' as u32;
        let (mut tmp, mut is_last) = (0u32, false);
        for c in s.chars().rev() {
            if c.is_ascii_digit() {
                match tmp.overflowing_add((c as u32) - ZERO) {
                    (x, true) => {
                        tmp = 1;
                        v.push(x);
                        is_last = false;
                    },
                    (x, false) => {
                        tmp = x;
                        is_last = true;
                    }
                }
            } else {
                return Err(NatError::new(IllegalCharEncounter, format!("illegal char {}", c)));
            }
        }
        
        if is_last {v.push(tmp)};
        Ok(Nat::from(v))
    }
    
    fn from_bin_str(s: &str) -> Result<Self, NatError> {
        let (mut tmp, mut is_last) = (0, false);
        let mut v = Vec::with_capacity(s.len() >> 5);
        for (i, c) in s.chars().rev().enumerate() {
            let x = if c == '0' {0} else if c == '1' {1} else {
                return Err(NatError::new(IllegalCharEncounter, format!("illegal char {}", c)));
            };
            
            if (i & 31) == 0 {
                is_last = if i > 31 {
                    v.push(tmp);
                    false
                } else {
                    true
                };
                tmp = x;
            } else {
                tmp += x << i;
                is_last = true;
            }
        }
        
        if is_last {v.push(tmp);}
        
        Ok(Nat::from(v))
    }
    
    fn from_oct_str(s: &str) -> Result<Self, NatError> {
        const ZERO: u32 = '0' as u32;
        let (mut tmp, mut i, mut is_last) = (0, 0, false);
        let mut v = Vec::with_capacity(s.len() / 10);
        
        for c in s.chars().rev() {
            if c >= '0' && c <= '7' {
                let n = (c as u32) - ZERO;
                
                if (i + 3) >= 29 {
                    let x = ((1 << (32 - i)) - 1) & n;
                    tmp += x << (32 - i);
                    v.push(tmp);
                    tmp = n - x;
                    i = (i + 3) - 32;
                    is_last = false;
                } else {
                    tmp += n << i;
                    i += 3;
                    is_last = true;
                }
            } else {
                return Err(NatError::new(IllegalCharEncounter, format!("illegal char {}", c)));
            }
        }

        if is_last {v.push(tmp);}
        Ok(Nat::from(v))
    }
    
    fn from_hex_str(s: &str) -> Result<Self, NatError> {
        const ZERO: u32 = '0' as u32;
        const LA: u32 = 'a' as u32;
        const BA: u32 = 'A' as u32;
        let (mut tmp, mut is_last) = (0, false);
        let mut v = Vec::with_capacity(s.len() >> 3);
        
        for (i, c) in s.chars().rev().enumerate() {
            let n = if c >= '0' && c <= '9' {(c as u32) - ZERO}
                else if c >= 'a' && c <= 'f' {(c as u32) - LA} 
                else if c >= 'A' && c <= 'F' {(c as u32) - BA}
                else {return Err(NatError::new(IllegalCharEncounter, format!("illegal char {}", c)))};
            
            if (i & 7) == 0 {
                is_last = if i > 7 {
                    v.push(tmp);
                    false
                } else {
                    true
                };
                tmp = n;
            } else {
                tmp += n << ((i & 7) << 2);
                is_last = true;
            }
        }
        
        if is_last {v.push(tmp);}
        Ok(Nat::from(v))
    }
    
    fn mul_inner(&self, max: &Self) -> Vec<u32> {
        const MASK: u64 = 0xffffffff;
        const SHR_BITS: u8 = 32;
    
        let (min, max, _) = Self::min_max(self, max);
        let min: Vec<u64> = min.iter().map(|&x| {x as u64}).collect();
        let max: Vec<u64> = max.iter().map(|&x| {x as u64}).collect();
        let mut nat = Nat::from(0u32);
        nat.as_mut_vec().reserve(min.len() + max.len());
    
        let mut round = Vec::with_capacity(min.len() + max.len());
        min.iter().enumerate().for_each(|(i, &a)| {
            round.clear();
            // 每一轮乘max都左移32位, 额外留出32位作为上一次单步乘的进位
            round.resize(i + 1, 0);
            max.iter().for_each(|&b| {
                let carry = round.pop().unwrap() as u64;
                let x = a * b;
                let (y, cy) = x.overflowing_add(carry);
                round.push((y & MASK) as u32);
                round.push((y >> SHR_BITS) as u32);
                if cy { round.push(1)};
            });
            nat += Nat::from(round.as_slice());
        });
    
        nat.trim_head_zero();
        nat.to_vec()
    }

    pub(super) fn add_inner(&self, rhs: &Self) -> Vec<u32> {
        let (min, max) = Nat::min_max_by_len(self.as_slice(), rhs.as_slice());

        let mut v = Vec::with_capacity(max.len());
        let mut carry = 0;
        min.iter().zip(max.iter()).for_each(|(&a, &b)| {
            let (x, cx) = a.overflowing_add(carry);
            let (y, cy) = b.overflowing_add(x);
            carry = if cx || cy {1} else {0};
            v.push(y);
        });

        max.iter().skip(min.len()).for_each(|&a| {
            let (x, cx) = a.overflowing_add(carry);
            carry  = if cx {1} else {0};
            v.push(x);
        });

        if carry > 0 {v.push(carry);}
        v
    }

    /// (abs(self-rhs), self >= rhs)
    pub(super) fn sub_inner_with_sign(&self, rhs: &Self) -> (Vec<u32>, bool) {
        let mut v = Vec::new();
        let mut carry = 0;
        let (min, max, is_great) = Self::min_max(&self, &rhs);
        max.iter().zip(min.iter()).for_each(|(&a, &b)| {
            let (x, cx) = a.overflowing_sub(carry);
            let (y, cy) = x.overflowing_sub(b);
            carry = if cx || cy {1} else {0};
            v.push(y);
        });

        max.iter().skip(min.num()).for_each(|&a| {
            let (x, cx) = a.overflowing_sub(carry);
            carry = if cx {1} else {0};
            v.push(x);
        });

        Self::trim_head_zero_(&mut v);
        (v, is_great)
    }

    pub(super) fn sub_inner(&self, rhs: &Self) -> Vec<u32> {
        self.sub_inner_with_sign(rhs).0
    }

    /// (abs(self-rhs), self >= rhs)
    pub fn sub_with_sign(&self, rhs: Self) -> (Nat, bool) {
        if self.is_nan() || rhs.is_nan() {
            (Nat::default(), false)
        } else {
            let x = self.sub_inner_with_sign(&rhs);
            (Nat::from(x.0), x.1)
        }
    }
    
    /// self -= rhs;
    /// self >= rhs
    pub fn sub_assign_with_sign(&mut self, rhs: Self) -> bool {
        if self.is_nan() || rhs.is_nan() {
            self.clear();
            false
        } else {
            let x = self.sub_inner_with_sign(&rhs);
            self.clear();
            self.as_mut_vec().extend_from_slice(x.0.as_slice());
            x.1
        }
    }
    
    pub(super) fn shl_inner(&self, rhs: &usize) -> Vec<u32> {
        let (num, nom) = (rhs >> 5, rhs & 31);
        let mut v = Vec::with_capacity(num + self.num());
        v.resize(num, 0);

        let nom_c = 32 - nom;
        if nom == 0 {
            v.extend_from_slice(self.as_slice());
        } else {
            let mut pre = 0;
            self.iter().for_each(|&a| {
                let val = (a << nom) | pre;
                pre = a >> nom_c;
                v.push(val);
            });
            if pre > 0 {v.push(pre);}
        }
        v
    }

    pub(super) fn shr_inner(&self, rhs: &usize) -> Vec<u32> {
        let (num, nom) = (rhs >> 5, rhs & 31);

        if nom == 0 {
            self.iter().skip(num).map(|&x|{x}).collect()
        } else {
            let mut v = Vec::with_capacity(self.num().saturating_sub(num));
            let (mut pre, mask, nom_c) = (0, (1 << nom) - 1, 32 - nom);
            self.iter().skip(num).for_each(|&a| {
                let val = (a & mask) << nom_c;
                v.push(val | pre);
                pre = a >> nom;
            });
            if pre > 0 { v.push(pre); }
            v
        }
    }

    pub(super) fn div_inner(&self, rhs: &Self) -> Vec<u32> {
        let mut a = self.deep_clone();
        
        assert_ne!(rhs, &0u32, "The dividend must not be 0");
    
        let one = Nat::from(1u32);
        let mut result = Nat::from(0u32);
        while a >= rhs.clone() {
            let mut c = rhs.deep_clone();
            let mut i = 0;
            while a >= c {
                a -= c.clone();
                result += one.clone() << i;
                i += 1;
                c <<= 1;
            }
        }
    
        result.to_vec()
    }
    
    pub(super) fn rem_inner(&self, rhs: &Self) -> Vec<u32> {
        let mut a = self.deep_clone();

        assert_ne!(rhs, &0u32, "The modulus must not be 0");

        let mut result = Nat::from(0u32);
        while a >= rhs.clone() {
            let mut c = rhs.deep_clone();
            while a >= c {
                result = a.deep_clone();
                a -= c.clone();
                c <<= 1;
            }
        }

        result.to_vec()
    }

    pub(super) fn bitand_inner(&self, rhs: &Self) -> Vec<u32> {
        let (min, max) = Self::min_max_by_len(self.as_slice(), rhs.as_slice());
        let mut v = Vec::with_capacity(min.len());
        
        min.iter().zip(max.iter()).for_each(|(&a, &b)| {
            v.push(a & b);
        });
        
        Self::trim_head_zero_(&mut v);
        
        v
    }
    
    pub(super) fn bitor_inner(&self, rhs: &Self) -> Vec<u32> {
        let (min, max) = Self::min_max_by_len(self.as_slice(), rhs.as_slice());
        let mut v = Vec::with_capacity(max.len());

        min.iter().zip(max.iter()).for_each(|(&a, &b)| {
            v.push(a | b);
        });
        
        max.iter().skip(min.len()).for_each(|&a| {
            v.push(a);
        });
        Self::trim_head_zero_(&mut v);
        
        v
    }
    
    pub(super) fn bitxor_inner(&self, rhs: &Self) -> Vec<u32> {
        let (min, max) = Self::min_max_by_len(self.as_slice(), rhs.as_slice());
        let mut v = Vec::with_capacity(max.len());

        min.iter().zip(max.iter()).for_each(|(&a, &b)| {
            v.push(a ^ b);
        });

        max.iter().skip(min.len()).for_each(|&a| {
            v.push(a ^ 0);
        });
        Self::trim_head_zero_(&mut v);
        
        v
    }
    
    pub(super) fn not_inner(&self) -> Vec<u32> {
        let mut v = Vec::with_capacity(self.num());
        
        self.iter().for_each(|&a| {
            v.push(!a);
        });
        Self::trim_head_zero_(&mut v);
        v
    }
}

impl Default for Nat {
    fn default() -> Self {
        Nat {nat: Rc::new(Cell::new(Vec::new()))}
    }
}

nat_from_basic!(u8, u16, u32, u64, u128);

impl From<Vec<u32>> for Nat {
    /// little endian
    fn from(x: Vec<u32>) -> Self {
        let mut x = x;
        Self::trim_head_zero_(&mut x);
        
        Nat {nat: Rc::new(Cell::new(x))}
    }
}

impl From<&[u32]> for Nat {
    /// little endian
    fn from(x: &[u32]) -> Self {
        let mut x = x.to_vec();
        Self::trim_head_zero_(&mut x);
        
        Nat {nat: Rc::new(Cell::new(x))}
    }
}

impl From<&[u8]> for Nat {
    /// little endian
    fn from(x: &[u8]) -> Self {
        const MASK: usize = 3;
        let mut v = Vec::with_capacity((x.len() + MASK) >> 2);
        let mut tmp = 0;
        x.iter().enumerate().for_each(|(i, &ele)| {
            if (i & MASK) == 0 {
                if i > MASK {
                    v.push(tmp);
                }
                tmp = ele as u32;
            } else {
                tmp += (ele as u32) << ((i & MASK) << 3);
            }
        });
        
        Self::trim_head_zero_(&mut v);
        Nat {nat: Rc::new(Cell::new(v))}
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

nat_fmt!((Binary, "{:032b}"), (LowerHex, "{:08x}"), (Debug, "{:08x}"), (UpperHex, "{:08X}"));

impl Octal for Nat {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.is_nan() {
            return write!(f, "{}", "NaN");
        }

        let mut nat_str = Vec::with_capacity(self.num() * 11);

        let mut pre = 0u32;
        for (i, &ele) in self.as_vec().iter().enumerate() {
            let tmp = match i % 3 {
                0 => {
                    (ele, ele >> 30)
                },
                1 => {
                    let val = ((ele & 0x1) << 2) | pre;
                    let s = format!("{:o}", val);
                    nat_str.push(s);
                    (ele >> 1, ele >> 31)
                },
                _ => {
                    let val = ((ele & 0x3) << 1) | pre;
                    let s = format!("{:o}", val);
                    nat_str.push(s);
                    (ele >> 2, 0)
                },
            };
            
            pre = tmp.1;
            for idx in 0..10u32 {
                let val = (tmp.0 >> (idx * 3)) & 0x7u32;
                let s = format!("{:o}", val);
                nat_str.push(s);
            }
        }

        if pre > 0 {
            let s = format!("{:o}", pre);
            nat_str.push(s);
        }

        match nat_str.last_mut() {
            Some(x) => {
                let mut y = String::with_capacity(x.len());
                y.push_str(x.as_str().trim_start_matches('0'));
                x.clear();
                x.push_str(y.as_str());
            },
            None => {},
        }

        nat_str.reverse();
        let s = nat_str.as_slice().join("");
        write!(f, "{}", s)
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

nat_eq_basic!(u8, u16, u32, u64, u128);

impl PartialOrd for Nat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.is_nan() || other.is_nan() {
            return None;
        }
        
        if self.num() < other.num() {
            Some(Ordering::Less)
        } else if self.num() > other.num() {
            Some(Ordering::Greater)
        } else {
            for (&a, &b) in self.iter().zip(other.iter()) {
                if a < b {
                    return Some(Ordering::Less);
                } else if a > b {
                    return Some(Ordering::Greater);
                }
            }
            Some(Ordering::Equal)
        }
    }
}

nat_ord_basic!(u8, u16, u32, u64, u128);

nat_arith_ops!((Nat, Add, AddAssign, add, add_assign, add_inner, |rhs: &Nat| {rhs.is_nan()}),
    (Nat, Sub, SubAssign, sub, sub_assign, sub_inner, |rhs: &Nat| {rhs.is_nan()}),
    (usize, Shl, ShlAssign, shl, shl_assign, shl_inner, |_rhs: &usize| {false}),
    (usize, Shr, ShrAssign, shr, shr_assign, shr_inner, |_rhs: &usize| {false}),
    (Nat, Div, DivAssign, div, div_assign, div_inner, |rhs: &Nat| {rhs.is_nan()}),
    (Nat, Rem, RemAssign, rem, rem_assign, rem_inner, |rhs: &Nat| {rhs.is_nan()}),
    (Nat, Mul, MulAssign, mul, mul_assign, mul_inner, |rhs: &Nat| {rhs.is_nan()}),
    (Nat, BitAnd, BitAndAssign, bitand, bitand_assign, bitand_inner, |rhs: &Nat| {rhs.is_nan()}),
    (Nat, BitOr, BitOrAssign, bitor, bitor_assign, bitor_inner, |rhs: &Nat| {rhs.is_nan()}),
    (Nat, BitXor, BitXorAssign, bitxor, bitxor_assign, bitxor_inner, |rhs: &Nat| {rhs.is_nan()})
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

