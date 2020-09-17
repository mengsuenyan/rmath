use crate::bigint::Nat;

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64 as march;

#[cfg(target_arch = "x86")]
use std::arch::x86 as march;


impl Nat {
    unsafe fn add_inner_by_adcx(lhs: &mut Self, rhs: &Self) {
        let (lhs, rhs) = (lhs.as_mut_vec(), rhs.as_vec());
        let (lhs_len, rhs_len) = (lhs.len(), rhs.len());
        let (lhs_itr, rhs_itr) = (lhs.iter_mut(), rhs.iter());
        let mut carry = 0;
        
        lhs_itr.zip(rhs_itr).for_each(|(a, &b)| {
            carry = march::_addcarryx_u32(carry, *a, b, a);
        });
        
        if lhs_len >= rhs_len {
            lhs.iter_mut().skip(rhs_len).for_each(|a| {
                carry = march::_addcarryx_u32(carry, *a, 0, a);
            });
        } else {
            rhs.iter().skip(lhs_len).for_each(|&b| {
                let mut out = 0;
                carry = march::_addcarryx_u32(carry, 0, b, &mut out);
                lhs.push(out);
            });
        }
        if carry > 0 {lhs.push(carry as u32);}
    }
    
    pub(super) fn add_inner(&mut self, rhs: &Self) {
        unsafe {
            Nat::add_inner_by_adcx(self, rhs)
        }
    }

    unsafe fn sub_inner_with_sign_by_sbb(&mut self, rhs: &Self) -> bool {
        let is_ge = *self >= *rhs;
        if !is_ge {
            self.as_mut_vec().resize(rhs.num(), 0);
        }
        let mut c = 0;
        self.iter_mut().zip(rhs.iter()).for_each(|(a, &b)| {
            c = if is_ge {
                march::_subborrow_u32(c, *a, b, a)
            } else {
                march::_subborrow_u32(c, b, *a, a)
            };
        });
        
        if is_ge && c > 0 {
            for a in self.iter_mut().skip(rhs.num()) {
                c = march::_subborrow_u32(c, *a, 0, a);
                if c == 0 {
                    break;
                }
            }
        }
        
        self.trim_head_zero();
        is_ge
    }
    
    /// (abs(self-rhs), self >= rhs)
    pub(super) fn sub_inner_with_sign(&mut self, rhs: &Self) -> bool {
        unsafe {
            self.sub_inner_with_sign_by_sbb(rhs)
        }
    }
    
    pub(super) fn sub_inner(&mut self, rhs: &Self) {
        self.sub_inner_with_sign(rhs);
    }

    pub(super) fn add_inner_basic(&mut self, rhs: &u32) {
        unsafe {self.add_inner_basic_by_adcx(*rhs)}
    }
    
    unsafe fn add_inner_basic_by_adcx(&mut self, mut rhs: u32) {
        let mut carry = 0;
        self.iter_mut().for_each(|a| {
            carry = march::_addcarryx_u32(carry, *a, rhs, a);
            rhs = 0;
        });
        if carry > 0 {self.as_mut_vec().push(carry as u32);}
    }

    pub(super) fn sub_inner_basic(&mut self, rhs: &u32) {
        if self.num() > 1 {
            unsafe {self.sub_inner_basic_by_sbb(*rhs)};
        } else {
            match self.as_mut_vec().last_mut() {
                Some(x) => {
                    *x = if *x < *rhs {
                        *rhs - *x
                    } else {
                        *x - *rhs
                    };
                },
                None => {},
            }
        }
    }
    
    unsafe fn sub_inner_basic_by_sbb(&mut self, mut rhs: u32) {
        let mut c = 0;
        self.iter_mut().for_each(|x| {
            c = march::_subborrow_u32(c, *x, rhs, x);
            rhs = 0;
        });
    }
    
    
}