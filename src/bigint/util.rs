

/// normalize returns a normal number y and exponent exp
/// satisfying x == y × 2**exp. It assumes x is finite and non-zero.
fn normalize(x: f64) -> (f64, isize) {
    let smallest_normal: f64 = 2.2250738585072014e-308; // 2**-1022
    let fexp: f64 = ((1u32 << 26) as f64) *((1u32 << 26) as f64);
    if x.abs() < smallest_normal {
        (x * fexp, -52)
    } else {
        (x, 0)
    }
}

/// Frexp breaks f into a normalized fraction 
/// and an integral power of two.  
/// It returns frac and exp satisfying f == frac × 2**exp, 
/// with the absolute value of frac in the interval [½, 1).  
///
/// Special cases are:  
///	Frexp(±0) = ±0, 0  
///	Frexp(±Inf) = ±Inf, 0  
///	Frexp(NaN) = NaN, 0  
pub(super) fn frexp(f: f64) -> (f64, isize) {
    if f == 0f64 {
        (f, 0)
    } else if f.is_infinite() || f.is_nan() {
        (f, 0)
    } else {
        let (mask, shift, bias) = (0x7ff, 52, 0x3ffu64);
        let (f, mut exp) = normalize(f);
        let x = f.to_bits();
        exp += (((x >> shift) & mask) as isize) - (bias as isize) + 1;
        let x = x & (!(mask << shift));
        let x = x | ((bias - 1) << shift);
        let frac = f64::from_bits(x);
        (frac, exp)
    }
}

/// ldexp is the inverse of Frexp.
/// It returns frac × 2**exp.
///
/// Special cases are:
///	ldexp(±0, exp) = ±0
///	ldexp(±Inf, exp) = ±Inf
///	ldexp(NaN, exp) = NaN
pub(super) fn ldexp(frac: f64, exp: isize) -> f64 {
    if frac == 0f64 {
        frac
    } else if frac.is_infinite() || frac.is_nan() {
        frac
    } else {
        let (shift, mask, bias) = (52, 2047, 1023);
        let (frac, e) = normalize(frac);
        let mut exp = exp + e;
        let x = frac.to_bits();
        exp += (((x >> shift) as isize) & mask) - bias;
        if exp < -1075 {
            // underflow
            (0f64).copysign(frac)
        } else if exp > 1023 {
            //overflow
            if frac < 0f64 {
                std::f64::NEG_INFINITY
            } else {
                std::f64::INFINITY
            }
        } else {
            let m = if exp < -1022 {
                // sub-normal
                exp += 53;
                1.0f64 / (((1u32 << 27) as f64) * ((1u32 << 26) as f64))
            } else {
                1.0f64
            };
            let x = x & !((mask as u64) << shift);
            let x = x | (((exp + bias) as u64) << shift);
            m * f64::from_bits(x)
        }
    }
}