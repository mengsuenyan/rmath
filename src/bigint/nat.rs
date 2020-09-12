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
    
    #[allow(unused)]
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

    #[allow(unused)]
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
        
        Err(NatError::new(BeginWithIllegalChar, "all char is +"))
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
            let mut itr = self.iter().skip(num);
            match itr.next() {
                Some(&x) => {pre = x >> nom;},
                None => {v.push(0);},
            }
            itr.for_each(|&a| {
                let val = (a & mask) << nom_c;
                v.push(val | pre);
                pre = a >> nom;
            });
            if pre > 0 { v.push(pre); }
            v
        }
    }

    pub(super) fn div_inner(&self, rhs: &Self) -> Vec<u32> {
        assert_ne!(rhs, &0u32, "The divisor must not be 0");
        
        if self < rhs {
            return vec![0];
        }
        
        let (dividend_len, divisor_len) = (self.bits_len(), rhs.bits_len());
        if dividend_len == divisor_len {
            return vec![1];
        }
        
        let one = Nat::from(1u32);
        let mut nat = Nat::from(0u32);
        let mut sc = self.deep_clone();
        loop {
            if sc >= rhs.clone() {
                let mut shift = sc.bits_len() - divisor_len;
                let mut den = rhs.clone() << shift;
                while den > sc {
                    den >>= 1;
                    shift -= 1;
                }
                
                sc -= den;
                nat += one.clone() << shift;
            } else {
                break;
            }
        }
        
        nat.into_vec()
    }

    pub(super) fn rem_inner(&self, rhs: &Self) -> Vec<u32> {
        assert_ne!(rhs, &0u32, "The modulus must not be 0");
        
        if self < rhs {
            return self.to_vec();
        }
        
        let divisor_len = rhs.bits_len();
        let mut sc = self.deep_clone();
        loop {
            if sc.clone() < rhs.clone() {
                break;
            } else {
                let shift = sc.bits_len() - divisor_len;
                let mut den = rhs.clone() << shift;
                if den.clone() > sc.clone() {
                    den >>= 1;
                }
                sc -= den;
            }
        }
        
        sc.into_vec()
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
        
        if self == &0u32 {if b.clone() == 0u32 {Nat::from(1u32)} else {Nat::from(0u32)}}
        else if b.clone() == 0u32 {Nat::from(1u32)}
        else {
            let blen = b.bits_len();
            let mut pre = self.deep_clone();
            let mut cur = if b.is_set_bit_(0) {self.deep_clone()} else {Nat::from(1u32)};
            (1..blen).for_each(|i| {
                pre *= pre.clone();
                if b.is_set_bit_(i) {
                    cur *= pre.clone();
                }
            });

            cur
        }
    }
    
    /// (self ^ b) mod n, self ^ b if n == 0
    /// 
    /// (a*b) mod c = ((a mod c) * (b mod c)) mod c
    pub fn pow_mod(&self, b: Nat, n: Nat) -> Nat {
        if self.is_nan() || b.is_nan() || n.is_nan() { return Nat::nan(); }
        
        if n == 0u32 {
            self.pow(b)
        } else if n == 1u32 {
            Nat::from(0u32)
        } else {
            // 反复平方法
            let mut d = Nat::from(1u32);
            let sm = self.clone() % n.clone();
            (0..b.bits_len()).rev().for_each(|i| {
                d *= d.clone();
                d %= n.clone();
                if b.is_set_bit_(i) {
                    d *= sm.clone();
                    d %= n.clone();
                }
            });
            d.clone()
        }
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

nat_fmt!((Binary, "{:032b}", "0b"), (LowerHex, "{:08x}", "0x"), (Debug, "{:08x}", "0x"), (UpperHex, "{:08X}", "0X"));

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
        nat_str.reverse();
        write!(f, "{}", nat_str.join(""))
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
        
        if self.num() < other.num() {
            Some(Ordering::Less)
        } else if self.num() > other.num() {
            Some(Ordering::Greater)
        } else {
            for (&a, &b) in self.iter().rev().zip(other.iter().rev()) {
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

nat_ord_basic!(u8, u16, u32, u64, u128, usize);

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

