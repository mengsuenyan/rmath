use crate::bigint::Nat;
use std::intrinsics::transmute;

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64 as march;

#[cfg(target_arch = "x86")]
use std::arch::x86 as march;

impl Nat {
    #[target_feature(enable = "avx2")]
    unsafe fn mul_manuual_by_avx2(min: &[u32], max: &[u32]) -> Vec<u32> {
        let (minp, maxp) = (min.as_ptr(), max.as_ptr());
        let (minp, maxp): (*const i32, *const i32) = (transmute(minp), transmute(maxp));
        let (mut lpkg, mut rpkg) = (Vec::with_capacity(min.len()), Vec::with_capacity(max.len()));
        
        let mask = march::_mm256_set1_epi32(-1);
        (0..(min.len() as isize)).for_each(|i| {
            lpkg.push(march::_mm256_set1_epi32(minp.offset(i).read()));
        });
        let (len, bound) = ((max.len() & (!3)) as isize, max.len() as isize);
        (0..len).step_by(4).for_each(|i| {
            let (x0, x1, x2, x3) = (maxp.offset(i).read(), maxp.offset(i+1).read(),
                maxp.offset(i + 2).read(), maxp.offset(i + 3).read());
            rpkg.push(march::_mm256_setr_epi32(x0, 0, x1, 0, x2, 0, x3, 0));
        });
        if (len+2) < bound {
            let (x0, x1, x2, x3) = (maxp.offset(len).read(), maxp.offset(len+1).read(),
             maxp.offset(len+2).read(), 0);
            rpkg.push(march::_mm256_setr_epi32(x0, 0, x1, 0, x2, 0, x3, 0));
        } else if (len + 1) < bound {
            let (x0, x1, x2, x3) = (maxp.offset(len).read(), maxp.offset(len + 1).read(),
             0, 0);
            rpkg.push(march::_mm256_setr_epi32(x0, 0, x1, 0, x2, 0, x3, 0));
        } else if len < bound {
            let (x0, x1, x2, x3) = (maxp.offset(len).read(), 0, 0, 0);
            rpkg.push(march::_mm256_setr_epi32(x0, 0, x1, 0, x2, 0, x3, 0));
        };
        
        let mut r = Vec::with_capacity(lpkg.len());
        let v_len = min.len() + (((max.len() + 3) >> 2) << 2) - 1;
        let mut tmp0 = Vec::with_capacity(v_len);
        for (i, &l) in lpkg.iter().enumerate() {
            tmp0.clear();
            tmp0.resize(v_len, 0u64);
            let mut tmp0_ptr: *mut i64 = transmute(tmp0.as_mut_ptr());
            tmp0_ptr = tmp0_ptr.add(i);
            for &r in rpkg.iter() {
                let tmp1 = march::_mm256_mul_epu32(l, r);
                march::_mm256_maskstore_epi64(tmp0_ptr, mask, tmp1);
                tmp0_ptr = tmp0_ptr.add(4);
            }
            r.push(tmp0.clone());
        }
        
        let mut v = Vec::with_capacity(v_len);
        let mut pre = 0;
        const MASK: u64 = u32::MAX as u64;
        (0..v_len).for_each(|i| {
            let mut c = 0;
            let mut out = pre;
            r.iter().for_each(|y| {
                c += march::_addcarryx_u64(0, out, y[i], &mut out) as u64;
            });
            v.push((out & MASK) as u32);
            pre = (out >> 32) | (c << 32);
        });
        
        if pre > 0 {v.push((pre & MASK) as u32);}
        
        v
    }
    
    pub(super) fn mul_inner(&self, max: &Self) -> Vec<u32> {
        if self == &0u32 || max == &0u32 {vec![0]}
        else if self == &1u32 {max.to_vec()}
        else if max == &1u32 {self.to_vec()}
        else {
            let (min, max, _) = self.min_max(max);
            unsafe {Nat::mul_manuual_by_avx2(min.as_slice(), max.as_slice())}
        }
    }
}