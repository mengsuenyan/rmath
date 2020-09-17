use crate::bigint::Nat;

impl Nat {
    pub(super) fn mul_inner(&mut self, max: &Self) {
        const MASK: u64 = 0xffffffff;
        const SHR_BITS: u8 = 32;

        let (min, max, _) = Self::min_max(&*self, max);
        let min: Vec<u64> = min.iter().map(|&x| {x as u64}).collect();
        let max: Vec<u64> = max.iter().map(|&x| {x as u64}).collect();
        let nat = self.as_mut_vec();
        nat.reserve(min.len() + max.len());
        nat.clear();
        nat.push(0);

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
            self.add_inner(&Nat::from(round.as_slice()));
        });
        self.trim_head_zero();
    }

    pub(super) fn add_inner(&mut self, rhs: &Self) {
        let is_ge = *self >= *rhs;
        if !is_ge {
            self.as_mut_vec().resize(rhs.num(), 0);
        }
        
        let mut c = 0;
        self.iter_mut().zip(rhs.iter()).for_each(|(a, &b)| {
            let (x,cx) = a.overflowing_add(b);
            let (y, cy) = x.overflowing_add(c);
            *a = y;
            c = if cx || cy {1} else {0};
        });
        self.iter_mut().skip(rhs.num()).for_each(|a| {
            let (x, cx) = a.overflowing_add(c);
            *a = x;
            c = if cx {1} else {0};
        });
        
        if c > 0 {
            self.as_mut_vec().push(c);
        }
    }

    pub(super) fn sub_inner_with_sign(&mut self, rhs: &Self) -> bool {
        let is_ge = *self >= *rhs;
        if !is_ge {
            self.as_mut_vec().resize(rhs.num(), 0);
        }
        
        let mut c = 0;
        self.iter_mut().zip(rhs.iter()).for_each(|(a, &b)| {
            let (x, cx) = if is_ge {
                a.overflowing_sub(b)
            } else {
                b.overflowing_sub(*a)
            };
            let (y, cy) = x.overflowing_sub(c);
            *a = y;
            c = if cy || cx {1} else {0};
        });
        
        if is_ge && c > 0 {
            self.iter_mut().skip(rhs.num()).for_each(|a| {
                let (x, cx) = a.overflowing_sub(c);
                *a = x;
                c = if cx {1} else {0};
            });
        }
        
        self.trim_head_zero();
        
        is_ge
    }

    pub(super) fn sub_inner(&mut self, rhs: &Self) {
        self.sub_inner_with_sign(rhs);
    }

    pub(super) fn add_inner_basic(&mut self, rhs: &u32) {
        let mut c = 0;
        let mut rhs = *rhs;
        self.iter_mut().for_each(|a| {
            let (x, cx) = a.overflowing_add(rhs);
            let (y, cy) = x.overflowing_add(c);
            rhs = 0;
            *a = y;
            c = if cx || cy {1} else {0};
        });
        if c > 0 {
            self.as_mut_vec().push(c);
        }
    }

    pub(super) fn sub_inner_basic(&mut self, rhs: &u32) {
        if self.num() <= 1 {
            match self.as_mut_vec().first_mut() {
                Some(x) => {
                    *x = if *x < *rhs {
                        *rhs - *x
                    } else {
                        *x - *rhs
                    };
                },
                None => {},
            };
        } else {
            let mut rhs = *rhs;
            let mut c = 0;
            self.iter_mut().for_each(|a| {
                c = if rhs > 0 {
                    let (x, cx) = a.overflowing_sub(rhs);
                    let (y, cy) = x.overflowing_sub(c);
                    *a = y;
                    rhs = 0;
                    if cx || cy {1} else {0}
                } else {
                    let (x, cx) = a.overflowing_sub(c);
                    *a = x;
                    if cx {1} else {0}
                }
            });
            self.trim_head_zero();
        }
    }

}

