use crate::bigint::Nat;

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64 as march;

#[cfg(target_arch = "x86")]
use std::arch::x86 as march;


impl Nat {
    unsafe fn add_inner_by_adcx(min: &[u32], max: &[u32]) -> Vec<u32> {

        let mut v = Vec::with_capacity(max.len());
        let mut carry = 0;
        
        let mut min_itr = min.iter();
        for &a in max.iter() {
            let mut out = 0;
            match min_itr.next() {
                Some(&b) => {
                    carry = march::_addcarryx_u32(carry, a, b, &mut out);
                },
                None => {
                    carry = march::_addcarryx_u32(carry, a, 0, &mut out);
                },
            }
            v.push(out);
        }
        
        if carry > 0 {v.push(carry as u32);}
        
        v
    }
    
    pub(super) fn add_inner(&self, rhs: &Self) -> Vec<u32> {
        let (min, max) = Nat::min_max_by_len(self.as_slice(), rhs.as_slice());
        unsafe {
            Nat::add_inner_by_adcx(min, max)
        }
    }

    unsafe fn sub_inner_with_sign_by_sbb(&self, rhs: &Self) -> (Vec<u32>, bool) {
        let (min, max, is_great) = self.min_max(rhs);
        
        let mut v = Vec::with_capacity(max.num());
        let mut c = 0;
        let mut min_itr = min.iter();
        for &a in max.iter() {
            let mut out = 0;
            match min_itr.next() {
                Some(&b) => {
                    c = march::_subborrow_u32(c, a, b, &mut out);
                },
                None => {
                    c = march::_subborrow_u32(c, a, 0, &mut out);
                }
            }
            v.push(out);
        }
        
        (v, is_great)
    }
    
    /// (abs(self-rhs), self >= rhs)
    pub(super) fn sub_inner_with_sign(&self, rhs: &Self) -> (Vec<u32>, bool) {
        unsafe {Nat::sub_inner_with_sign_by_sbb(self, rhs)}
    }
    
    pub(super) fn sub_inner(&self, rhs: &Self) -> Vec<u32> {
        self.sub_inner_with_sign(rhs).0
    }
}