use crate::bigint::{Float, BigInt, Rat};
use std::fmt::{LowerExp, Formatter, UpperExp, Display, Debug};
use crate::bigint::bigint::BISign::Negative;
use crate::bigint::decimal::Decimal;
use std::str::FromStr;
use crate::bigint::float_err::{FloatError, FloatErrKind};
use crate::bigint::bigint::BISign;

impl Float {
    
    fn fmt_inner(&self, buf: &mut String, prec: usize, fmt_char: char) {
        buf.clear();
        
        if self.is_nan() {
            buf.push_str("NaN");
            return;
        }
        
        if self.form.is_zero() {
            buf.push('0');
            return;
        }
        
        if self.neg == Negative {
            buf.push('-');
        }
        
        if self.form.is_infinite() {
            if self.neg != Negative {
                buf.push('+');
            }
            
            buf.push_str("Inf");
            return;
        }
        
        if self.mant == 0u32 {
            buf.push('0');
            return;
        }
        
        let mut decimal = Decimal::new(&self.mant, self.exp - (self.mant.bits_len() as isize));
        decimal.round(1 + prec);
        match fmt_char {
            'e' | 'E' => {
                decimal.round( 1 + prec);
                Self::fmt_for_exp(buf, &decimal, prec, fmt_char);
            },
            'f' => {
                let n = decimal.exp + (prec as isize);
                if n >= 0 {
                    decimal.round(n as usize);
                }
                Self::fmt_for_display(buf, &decimal, prec);
            },
            _ => {
                unimplemented!();
            }
        }
    }
    
    /// d.ddde±dd
    fn fmt_for_exp(buf: &mut String, d: &Decimal, prec: usize, fmt_char: char) {
        buf.push(*d.mant.first().unwrap());
        
        if prec > 0 {
            buf.push('.');
            let (mut i, m) = (1, std::cmp::min(d.mant.len(), prec + 1));
            if i < m {
                d.mant.iter().skip(i).take(m-i).for_each(|&c| {buf.push(c);});
                i = m;
            }
            
            (i..=prec).for_each(|_| {buf.push('0');});
        }
        
        buf.push(fmt_char);
        let exp = if d.exp < 1 {
            buf.push('-');
            1 - d.exp
        } else {
            // buf.push('+');
            d.exp - 1
        } as usize;
        
        if exp < 10 {
            // at least 2 exponent digits
            buf.push('0');
        }
        let s = format!("{}", exp);
        buf.push_str(s.as_str());
    }
    
    fn fmt_for_display(buf: &mut String, d: &Decimal, prec: usize) {
        if d.exp > 0 {
            let m = std::cmp::min(d.mant.len(), d.exp as usize);
            d.mant.iter().take(m).for_each(|&c| {buf.push(c);});
            (m..(d.exp as usize)).for_each(|_| {buf.push('0');});
        } else {
            buf.push('0');
        }
        
        if prec > 0 {
            buf.push('.');
            (0..prec).for_each(|i| {buf.push(d[(d.exp as usize) + i]);});
        }
    }
}

impl LowerExp for Float {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let prec = if let Some(p) = f.precision() {p} else {7};
        let mut s = String::with_capacity(prec + 2 + (self.mant.bits_len() >> 3));
        
        self.fmt_inner(&mut s, prec, 'e');
        
        write!(f, "{}", s)
    }
}

impl UpperExp for Float {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let prec = if let Some(p) = f.precision() {p} else {7};
        let mut s = String::with_capacity(prec + 2 + (self.mant.bits_len() >> 3));
        self.fmt_inner(&mut s, prec, 'E');
        
        write!(f, "{}", s)
    }
}

impl Display for Float {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let prec = self.prec;
        let mut s = String::with_capacity(self.mant.bits_len() >> 3);
        
        self.fmt_inner(&mut s, prec, 'f');
        
        write!(f, "{}", s)
    }
}

impl Debug for Float {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let prec = self.prec;
        let mut s = String::with_capacity(self.mant.bits_len() >> 3);

        self.fmt_inner(&mut s, prec, 'f');

        write!(f, "{}", s)
    }
}

impl FromStr for Float {
    type Err = FloatError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();
        if s.is_empty() {
            return Err(FloatError::new(FloatErrKind::ParseStringWrong, "empty string"));
        }
        
        let (dot_idx, se_idx, ue_idx) = (s.find('.'), s.find('e'), s.find('E'));
        
        let e_idx = if se_idx.is_some() && ue_idx.is_some() {
            return Err(FloatError::new(FloatErrKind::ParseStringWrong, "invalid string"));
        } else {
            se_idx.xor(ue_idx)
        };
        
        if dot_idx.is_none() && e_idx.is_none() {
            return match BigInt::from_str(s) {
                Ok(n) => {
                    Ok(Float::from(n))
                },
                Err(e) => {
                    Err(FloatError::new(FloatErrKind::ParseStringWrong, e))
                },
            };
        }
        
        let (max_exp, min_exp) = (BigInt::from(Self::max_exp()), BigInt::from(Self::min_exp()));
        let (s, exp) = match e_idx {
            Some(idx) => {
                let es = &s[(idx+1)..];
                if es.is_empty() {
                    (s, 0)
                } else {
                    let e = match BigInt::from_str(es) {
                        Ok(x) => x,
                        Err(e) => {return Err(FloatError::new(FloatErrKind::ParseStringWrong, e));},
                    };
                    
                    if e < min_exp {
                        return Err(FloatError::new(FloatErrKind::ExponentUnderflow, format!("exp: {}", e)));
                    } else if e > max_exp {
                        return Err(FloatError::new(FloatErrKind::ExponentOverflow, format!("exp: {}", e)));
                    } else {
                        let mut tmp = 0;
                        for &x in e.nat.iter().rev() {
                            tmp <<= 32;
                            tmp |= x as isize;
                        }
                        
                        if e.sign == BISign::Negative {
                            tmp = -tmp;
                        }
                        
                        (&s[..idx], tmp)
                    }
                }
            },
            None => (s, 0),
        };
        
        let (mut buf_nu, mut buf_de) = (String::with_capacity(s.len()), String::with_capacity(s.len()));
        let exp = match dot_idx {
            Some(idx) => {
                buf_nu.push_str(&s[..idx]);
                buf_nu.push_str(&s[(idx+1)..]);
                exp - (s.len() - idx - 1) as isize
            },
            None => {
                buf_nu.push_str(s);
                exp
            }
        };
        
        if exp < 0 {
            buf_de.push('1');
            buf_de.push_str("0".repeat((-exp) as usize).as_str());
        } else {
            buf_nu.push_str("0".repeat(exp as usize).as_str());
        }
        
        let numerator = match BigInt::from_str(buf_nu.as_str()) {
            Ok(n) => n,
            Err(e) => {
                return Err(FloatError::new(FloatErrKind::ParseStringWrong, e));
            }
        };
        
        let denominator = match BigInt::from_str(buf_de.as_str()) {
            Ok(n) => n,
            Err(e) => {
                return Err(FloatError::new(FloatErrKind::ParseStringWrong, e));
            }
        };

        match Rat::from_frac_bigint(&numerator, &denominator) {
            Ok(r) => Ok(Float::from(r)),
            Err(e) => Err(FloatError::new(FloatErrKind::ParseStringWrong, e)),
        }
    }
}
