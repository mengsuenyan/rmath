use std::ops::Index;
use crate::bigint::Nat;
use std::fmt::{Display, Formatter};

const MAX_SHIFT: isize = 32 - 4;

/// A decimal represents an unsigned floating-point number in decimal representation.
/// The value of a non-zero decimal d is d.mant * 10**d.exp with 0.1 <= d.mant < 1,
/// with the most-significant mantissa digit at index 0. For the zero decimal, the
/// mantissa length and exponent are 0.
/// The zero value for decimal represents a ready-to-use 0.0.
pub(super) struct Decimal {
    pub(super) mant: Vec<char>,
    pub(super) exp: isize,
    pub(super) zero: char,
}

impl Decimal {
    /// Init initializes x to the decimal representation of m << shift (for
    /// shift >= 0), or m >> -shift (for shift < 0).
    pub(super) fn new(m: &Nat, mut shift: isize) -> Self {
        if m.is_nan() || m == &0u32 {
            Self {
                mant: vec![],
                exp: 0,
                zero: '0',
            }
        } else {
            let mut m = m.deep_clone();
            if shift < 0 {
                let ntz = m.trailling_zeros();
                let mut s = (-shift) as usize;
                if s >= ntz {
                    s = ntz;
                }
                m >>= s;
                shift += s as isize;
            }
            
            if shift > 0 {
                m <<= shift as usize;
                shift = 0;
            }
            
            let s = format!("{}", m);
            let mut n = s.len();
            let mut z = Self {
                mant: vec![],
                exp: n as isize,
                zero: '0',
            };
            
            for c in s.chars().rev() {
                if c == '0' {
                    n -= 1;
                }
            }
            s.chars().take(n).for_each(|c| {z.mant.push(c);});
            
            if shift < 0 {
                while shift < -MAX_SHIFT {
                    z.shr_inner(MAX_SHIFT as usize);
                    shift += MAX_SHIFT;
                }
                z.shr_inner((-shift) as usize);
            }
            
            z
        }
    }

    // shr implements x >> s, for s <= maxShift.
    fn shr_inner(&mut self, s: usize) {
        // Division by 1<<s using shift-and-subtract algorithm.

        let zero_char = '0' as u8;
        
        // pick up enough leading digits to cover first shift
        let (mut r, mut n) = (0, 0);
        for &c in self.mant.iter() {
            if (n >> s) == 0 {
                r += 1;
                n = (n * 10) + ((c as u8 - zero_char) as usize)
            }
        }
        
        if n == 0 {
            self.mant.clear();
            return;
        }
        
        while (n >> s) == 0 {
            r += 1;
            n *= 10;
        }
        self.exp += 1 - r;
        
        let (mut w, mask) = (0, (1 << s) - 1);
        let (mut r, len) = (r as usize, self.mant.len());
        while r < len {
            let c = self.mant[r] as u8;
            r += 1;
            let d = (n >> s) as u8;
            n &= mask;
            self.mant[w] = (d + zero_char) as char;
            w += 1;
            n = (n * 10) + (c - zero_char) as usize;
        }
        
        while n > 0 && w < len {
            let d = (n >> s) as u8;
            n &= mask;
            self.mant[w] = (d + zero_char) as char;
            w += 1;
            n = n * 10;
        }
        self.mant.truncate(w);
        
        while n > 0 {
            let d = (n >> s) as u8;
            n &= mask;
            self.mant.push((d + zero_char) as char);
            n = n * 10;
        }
        
        self.trim();
    }
    
    fn trim(&mut self) {
        let mut i = self.mant.len();
        for &c in self.mant.iter().rev() {
            if c == '0' {
                i -= 1;
            } else {
                break;
            }
        }
        
        self.mant.truncate(i);
        if i == 0 {
            self.exp = 0;
        }
    }

    /// shouldRoundUp reports if x should be rounded up
    /// if shortened to n digits. n must be a valid index
    /// for x.mant.
    fn is_should_round_up(&self, n: usize) -> bool {
        if self.mant[n] == '5' && (n + 1) == self.mant.len() {
            n > 0 && ((self.mant[n-1] as u8 - '0' as u8) & 1) != 0
        } else {
            self.mant[n] >= '5'
        }
    }

    /// round sets x to (at most) n mantissa digits by rounding it
    /// to the nearest even value with n (or fever) mantissa digits.
    /// If n < 0, x remains unchanged.
    pub(super) fn round(&mut self, n: usize) {
        if n < self.mant.len() {
            if self.is_should_round_up(n) {
                self.round_up(n);
            } else {
                self.round_down(n);
            }
        }
    }
    
    fn round_up(&mut self, mut n: usize) {
        if n < self.mant.len() {
            for &c in self.mant.iter().take(n).rev() {
                if c >= '9' {
                    n -= 1;
                } else {
                    break;
                }
            }
            
            if n == 0 {
                self.mant[0] = '1';
                self.mant.truncate(1);
                self.exp += 1;
                return;
            }

            // n > 0 && x.mant[n-1] < '9'
            self.mant[n-1] = (self.mant[n-1] as u8 + 1) as char;
            self.mant.truncate(n);
            // x already trimmed
        }
    }
    
    fn round_down(&mut self, n: usize) {
        if n < self.mant.len() {
            self.mant.truncate(n);
            self.trim();
        }
    }
}

impl Index<usize> for Decimal {
    type Output = char; 

    fn index(&self, index: usize) -> &Self::Output {
        if index < self.mant.len() {
            &self.mant[index]
        } else {
            &self.zero
        }
    }
}

impl Display for Decimal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut s = String::with_capacity(2 + ((-self.exp) as usize) + self.mant.len());
        if self.mant.is_empty() {
            s.push_str("NaN");
        } else if self.exp <= 0 {
            s.push_str("0.");
            (0..(-self.exp)).for_each(|_| {s.push('0');});
            self.mant.iter().for_each(|&c| {s.push(c);});
        } else if self.exp < (self.mant.len() as isize) {
            self.mant.iter().take(self.exp as usize).for_each(|&c| {s.push(c);});
            s.push('.');
            self.mant.iter().skip(self.exp as usize).for_each(|&c| {s.push(c);});
        } else {
            self.mant.iter().for_each(|&c| {s.push(c);});
            ((self.exp as usize)..self.mant.len()).for_each(|_| {s.push('0');});
        }
        
        write!(f, "{}", s)
    }
}