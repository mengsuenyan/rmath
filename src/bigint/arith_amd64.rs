#![allow(unused)]

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64 as march;

#[cfg(target_arch = "x86")]
use std::arch::x86 as march;

use std::mem::transmute;

#[inline]
pub(super) fn mul_ww(x: u32, y: u32) -> (u32, u32) {
    let o = [0u32;2];
    unsafe {
        let a = march::_mm_set1_pi32(transmute(x));
        let b = march::_mm_set1_pi32(transmute(y));
        let c = march::_mm_mul_su32(a, b);
        march::_mm_stream_pi(transmute(o.as_ptr()), c);
    }
    (o[1], o[0])
}


#[inline]
pub(super) fn mul_add_www(x: u32, y: u32, c: u32) -> (u32, u32) {
    let o = [0u32;2];
    unsafe {
        let a = march::_mm_set1_pi32(transmute(x));
        let b = march::_mm_set1_pi32(transmute(y));
        let c = march::_mm_set1_pi32(transmute(c));
        let tmp = march::_mm_mul_su32(a, b);
        let d = march::_mm_add_pi32(tmp, c);
        march::_mm_stream_pi(transmute(o.as_ptr()), c);
    }
    (o[1], o[0])
}


#[inline]
pub(super) fn div_ww(u1: u32, u0: u32, v: u32) -> (u32, u32) {
    let (z, v) = (((u1 as u64) << 32) + (u0 as u64), v as u64);
    ((z / v) as u32, (z % v) as u32)
}


pub(super) fn add_vv(z: &mut [u32], x: &[u32], y: &[u32]) -> u32 {
    z.iter_mut().zip(x.iter().zip(y.iter())).fold(0, |c, (zt, (&xt, &yt))| {
        unsafe {
            march::_addcarry_u32(c, xt, yt, zt)
        }
    }) as u32
}

pub(super) unsafe fn add_vv_inner(z: *mut u32, x: *const u32, y: *const u32, n: usize) -> u32 {
    (0..n).fold(0, |c, i| {
        march::_addcarry_u32(c, x.add(i).read(), y.add(i).read(), z.add(i).as_mut().unwrap())
    }) as u32
}


pub(super) fn sub_vv(z: &mut [u32], x: &[u32], y: &[u32]) -> u32 {
    z.iter_mut().zip(x.iter().zip(y.iter())).fold(0, |c, (zt, (&xt, &yt))| {
        unsafe {
            march::_subborrow_u32(c, xt, yt, zt)
        }
    }) as u32
}

pub(super) unsafe fn sub_vv_inner(z: *mut u32, x: *const u32, y: *const u32, n: usize) -> u32 {
    (0..n).fold(0, |c, i| {
        march::_subborrow_u32(c, x.add(i).read(), y.add(i).read(), z.add(i).as_mut().unwrap())
    }) as u32
}

pub(super) fn add_vw(z: &mut [u32], x: &[u32], y: u32) -> u32 {
    z.iter_mut().zip(x.iter()).enumerate().fold(0, |c, (i, (zt, &xt))| {
        unsafe {
            if i == 0 {
                march::_addcarry_u32(c, xt, y, zt)
            } else {
                march::_addcarry_u32(c, xt, 0, zt)
            }
        }
    }) as u32
}

pub(super) unsafe fn add_vw_inner(z: *mut u32, x: *const u32, y: u32, n: usize) -> u32 {
    (0..n).fold(0, |c, i|{
        if i == 0 {
            march::_addcarry_u32(c, x.add(i).read(), y, z.add(i).as_mut().unwrap())
        } else {
            march::_addcarry_u32(c, x.add(i).read(), 0, z.add(i).as_mut().unwrap())
        }
    }) as u32
}

pub(super) fn add_vw_large(z: &mut [u32], x: &[u32], y: u32) -> u32 {
    z.iter_mut().zip(x.iter()).enumerate().fold(0, |c, (i, (zt, &xt))| {
        unsafe {
            if i == 0 {
                march::_addcarry_u32(c, xt, y, zt)
            } else {
                if c != 0 {
                    march::_addcarry_u32(c, xt, 0, zt)
                } else {
                    *zt = xt;
                    0
                }
            }
        }
    }) as u32
}


pub(super) fn sub_vw(z: &mut [u32], x: &[u32], y: u32) -> u32 {
    z.iter_mut().zip(x.iter()).enumerate().fold(0, |c, (i, (zt, &xt))| {
        unsafe {
            if i == 0 {
                march::_subborrow_u32(c, xt, y, zt)
            } else {
                march::_subborrow_u32(c, xt, 0, zt)
            }
        }
    }) as u32
}

pub(super) unsafe fn sub_vw_inner(z: *mut u32, x: *const u32, y: u32, n: usize) -> u32 {
    (0..n).fold(0, |c, i|{
        let xt = x.add(i).read();
        let zt = z.add(i).as_mut().unwrap();
        if i == 0 {
            march::_subborrow_u32(c, xt, y, zt)
        } else {
            march::_subborrow_u32(c, xt, 0, zt)
        }
    }) as u32
}

pub(super) fn sub_vw_large(z: &mut [u32], x: &[u32], y: u32) -> u32 {
    z.iter_mut().zip(x.iter()).enumerate().fold(0, |c, (i, (zt, &xt))| {
        unsafe {
            if i == 0 {
                march::_subborrow_u32(c, xt, y, zt)
            } else {
                if c != 0 {
                    march::_subborrow_u32(c, xt, 0, zt)
                } else {
                    *zt = xt;
                    0
                }
            }
        }
    }) as u32
}

pub(super) fn shl_vu(z: &mut [u32], x: &[u32], s: usize) -> u32 {
    if s == 0 || x.is_empty(){
        z.copy_from_slice(x);
        return 0;
    }

    let s = s & 31;
    let ss = (32 - s) & 31;
    let c = x.last().unwrap() >> s;
    x.iter().rev().skip(1).zip(x.iter().rev().zip(z.iter_mut().rev())).for_each(|(&xt0, (&xt1, zt))| {
        *zt = (xt1 << s) | (xt0 >> ss);
    });
    z[0] = x[0] << s;
    c
}

pub(super) unsafe fn shl_vu_inner(z: *mut u32, x: *const u32, s: usize, n: usize) -> u32 {
    if s == 0 || n == 0 {
        std::ptr::copy(x, z, n);
        return 0;
    }

    let s = s & 31;
    let ss = (32-s) & 31;
    let c= x.add(n-1).read() >> ss;
    for i in (1..n).rev() {
        z.add(i).write((x.add(i).read() << s) | (x.add(i-1).read() >> ss));
    }
    z.write(x.read() << s);
    c
}

pub(super) fn shr_vu(z: &mut [u32], x: &[u32], s: usize) -> u32 {
    if s == 0 || x.is_empty(){
        z.copy_from_slice(x);
        return 0;
    }
    let s = s & 31;
    let ss = (32 - s) & 31;
    let c = x[0] << ss;
    x.iter().skip(1).zip(x.iter().zip(z.iter_mut())).for_each(|(&xt1, (&xt0, zt))| {
        *zt = (xt0 >> s) | (xt1 << ss);
    });
    *z.last_mut().unwrap() = x.last().unwrap() >> s;
    c
}

pub(super) unsafe fn shr_vu_inner(z: *mut u32, x: *const u32, s: usize, n: usize) -> u32 {
    if s == 0 || n == 0 {
        std::ptr::copy(x, z, n);
        return 0;
    }

    let s = s & 31;
    let ss = (32 - s) & 31;
    let c = x.read() << ss;
    for i in 0..(n-1) {
        let tmp = (x.add(i).read() >> s) | (x.add(i+1).read() << ss);
        z.add(i).write(tmp);
    }
    z.add(n-1).write(x.add(n-1).read() >> s);
    c
}

pub(super) fn mul_add_vww(z: &mut [u32], x: &[u32], y: u32, r: u32) -> u32 {
    z.iter_mut().zip(x.iter()).fold(r, |c, (zt, &xt)| {
        let (cc, tt) = mul_add_www(xt, y, c);
        *zt = tt;
        cc
    })
}

pub(super) fn add_mul_vvw(z: &mut [u32], x: &[u32], y: u32) -> u32 {
    z.iter_mut().zip(x.iter()).fold(0, |c, (zt, &xt)| {
        let (z1, z0) = mul_add_www(xt, y, *zt);
        let cc = unsafe {
            march::_addcarry_u32(0, z0, c, zt)
        } as u32;
        z1 + cc
    })
}

pub(super) unsafe fn add_mul_vvw_inner(z: *mut u32, x: *const u32, y: u32, n: usize) -> u32{
    (0..n).fold(0, |c, i| {
        let zt = z.add(i);
        let (z1, z0) = mul_add_www(x.add(i).read(), y, zt.read());
        let cc = march::_addcarry_u32(0, z0, c, zt.as_mut().unwrap()) as u32;
        z1 + cc
    })
}

pub(super) fn div_wvw(z: &mut [u32], xn: u32, x: &[u32], y: u32) -> u32 {
    z.iter_mut().zip(x.iter()).fold(xn, |r, (zt, &xt)| {
        let (tmpz, tmpr) = div_ww(r, xt, y);
        *zt = tmpz;
        tmpr
    })
}
