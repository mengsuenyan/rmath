//! this is convert from the golang source code.

#![allow(unused)]

/// z = x*y   
/// (z >> 32, z & 0xffffffff)  
#[inline]
pub(super) fn mul_ww(x: u32, y: u32) -> (u32, u32) {
    let z = (x as u64) * (y as u64);
    ((z >> 32) as u32, (z & 0xffffffff) as u32)
}

/// z = x*y + c   
/// (z >> 32, z & 0xffffffff)  
#[inline]
pub(super) fn mul_add_www(x: u32, y: u32, c: u32) -> (u32, u32) {
    let z = ((x as u64) * (y as u64)) + (c as u64);
    ((z >> 32) as u32, (z & 0xffffffff) as u32)
}

/// (q, r)  
/// q = ((u1 << 32) + u0 - r) / v
/// 
/// # panics
/// 
/// v == 0 or v <= u1
#[inline]
pub(super) fn div_ww(u1: u32, u0: u32, v: u32) -> (u32, u32) {
    let z = ((u1 as u64) << 32) + (u0 as u64);
    let v = v as u64;
    ((z / v) as u32, (z % v) as u32)
}

/// z = x + y   
/// return carry   
pub(super) fn add_vv(z: &mut Vec<u32>, x: &Vec<u32>, y: &Vec<u32>) -> u32 {
    z.clear();
    x.iter().zip(y.iter()).fold(0, |c, (&xt, &yt)| {
        let (tt0, cc0) = xt.overflowing_add(yt);
        let (tt, cc) = tt0.overflowing_add(c);
        z.push(tt);
        if cc0 || cc {1} else {0}
    })
}

/// z = x - y   
/// return carry   
pub(super) fn sub_vv(z: &mut Vec<u32>, x: &Vec<u32>, y: &Vec<u32>) -> u32 {
    z.clear();
    x.iter().zip(y.iter()).fold(0, |c, (&xt, &yt)| {
        let (tt0, cc0) = xt.overflowing_sub(yt);
        let (tt, cc) = tt0.overflowing_sub(c);
        z.push(tt);
        if cc0 || cc {1} else {0}
    })
}

pub(super) fn add_vw(z: &mut Vec<u32>, x: &Vec<u32>, y: u32) -> u32 {
    z.clear();
    x.iter().fold(y, |c, &xt| {
        let (tt, cc) = xt.overflowing_add(c);
        z.push(tt);
        if cc {1} else {0}
    })
}

pub(super) fn add_vw_large(z: &mut Vec<u32>, x: &Vec<u32>, y: u32) -> u32 {
    let mut c = y;
    
    z.clear();
    for (i, &xt) in x.iter().enumerate() {
        if c == 0 {
            z.extend_from_slice(&x.as_slice()[i..]);
            return 0;
        } else {
            let (tt, cc) = xt.overflowing_add(c);
            c = if cc{1} else {0};
            z.push(tt);
        }
    }
    c
}

pub(super) fn sub_vw(z: &mut Vec<u32>, x: &Vec<u32>, y: u32) -> u32 {
    z.clear();
    x.iter().fold(y, |c, &xt| {
        let (tt, cc) = xt.overflowing_sub(c);
        z.push(tt);
        if cc {1} else {0}
    })
}

pub(super) fn sub_vw_large(z: &mut Vec<u32>, x: &Vec<u32>, y: u32) -> u32 {
    let mut c = y;
    z.clear();
    
    for (i, &xt) in x.iter().enumerate() {
        if c == 0 {
            z.extend_from_slice(&x.as_slice()[i..]);
            return 0;
        } else {
            let (tt, cc) = xt.overflowing_sub(c);
            c = if cc{1} else {0};
            z.push(tt);
        }
    }
    
    c
}

pub(super) fn shl_vu(z: &mut Vec<u32>, x: &Vec<u32>, s: usize) -> u32 {
    z.clear();
    if s == 0 || x.is_empty(){
        z.extend_from_slice(x.as_slice());
        return 0;
    }
    
    z.resize(x.len(), 0);
    let s = s & 31;
    let ss = (32 - s) & 31;
    x.iter().rev().skip(1).zip(x.iter().rev().zip(z.iter_mut().rev())).for_each(|(&xt0, (&xt1, zt))| {
        *zt = (xt1 << s) | (xt0 >> ss);
    });
    z[0] = x[0] << s;
    x.last().unwrap() >> s
}

pub(super) fn shr_vu(z: &mut Vec<u32>, x: &Vec<u32>, s: usize) -> u32 {
    z.clear();
    if s == 0 || x.is_empty(){
        z.extend_from_slice(x.as_slice());
        return 0;
    }
    z.resize(x.len(), 0);
    let s = s & 31;
    let ss = (32 - s) & 31;
    
    x.iter().skip(1).zip(x.iter().zip(z.iter_mut())).for_each(|(&xt1, (&xt0, zt))| {
        *zt = (xt0 >> s) | (xt1 << ss);
    });
    *z.last_mut().unwrap() = x.last().unwrap() >> s;
    x[0] << ss
}

pub(super) fn mul_add_vww(z: &mut Vec<u32>, x: &Vec<u32>, y: u32, r: u32) -> u32 {
    z.clear();
    x.iter().fold(r, |c, &xt| {
        let (cc, zt) = mul_add_www(xt, y, c);
        z.push(zt);
        cc
    })
}

/// z = x*y + z
pub(super) fn add_mul_vvw(z: &mut Vec<u32>, x: &Vec<u32>, y: u32) -> u32 {
    z.iter_mut().zip(x.iter()).fold(0, |c, (zt, &xt)| {
        let (z1, z0) = mul_add_www(xt, y, *zt);
        let (lo, cc) = z0.overflowing_add(c);
        *zt = lo;
        if cc {1 + z1} else {z1}
    })
}

pub(super) fn div_wvw(z: &mut Vec<u32>, xn: u32, x: &Vec<u32>, y: u32) -> u32 {
    z.clear();
    z.resize(x.len(), 0);
    z.iter_mut().zip(x.iter()).fold(xn, |r, (zt, &xt)| {
        let (tmpz, tmpr) = div_ww(r, xt, y);
        *zt = tmpz;
        tmpr
    })
}