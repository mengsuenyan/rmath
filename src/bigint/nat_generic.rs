use crate::bigint::Nat;

impl Nat {
    pub(super) fn mul_inner(&self, max: &Self) -> Vec<u32> {
        const MASK: u64 = 0xffffffff;
        const SHR_BITS: u8 = 32;

        let (min, max, _) = Self::min_max(self, max);
        let min: Vec<u64> = min.iter().map(|&x| {x as u64}).collect();
        let max: Vec<u64> = max.iter().map(|&x| {x as u64}).collect();
        let mut nat = Nat::from(0u32);
        nat.as_mut_vec().reserve(min.len() + max.len());

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
            nat += Nat::from(round.as_slice());
        });

        nat.to_vec()
    }

    pub(super) fn add_inner(&self, rhs: &Self) -> Vec<u32> {
        let (min, max) = Nat::min_max_by_len(self.as_slice(), rhs.as_slice());

        let mut v = Vec::with_capacity(max.len());
        let mut carry = 0;
        min.iter().zip(max.iter()).for_each(|(&a, &b)| {
            let (x, cx) = a.overflowing_add(carry);
            let (y, cy) = b.overflowing_add(x);
            carry = if cx || cy {1} else {0};
            v.push(y);
        });

        max.iter().skip(min.len()).for_each(|&a| {
            let (x, cx) = a.overflowing_add(carry);
            carry  = if cx {1} else {0};
            v.push(x);
        });

        if carry > 0 {v.push(carry);}
        v
    }

    /// (abs(self-rhs), self >= rhs)
    pub(super) fn sub_inner_with_sign(&self, rhs: &Self) -> (Vec<u32>, bool) {
        let mut v = Vec::new();
        let mut carry = 0;
        let (min, max, is_great) = Self::min_max(&self, &rhs);
        max.iter().zip(min.iter()).for_each(|(&a, &b)| {
            let (x, cx) = a.overflowing_sub(carry);
            let (y, cy) = x.overflowing_sub(b);
            carry = if cx || cy {1} else {0};
            v.push(y);
        });

        max.iter().skip(min.num()).for_each(|&a| {
            let (x, cx) = a.overflowing_sub(carry);
            carry = if cx {1} else {0};
            v.push(x);
        });

        Self::trim_head_zero_(&mut v);
        (v, is_great)
    }

    pub(super) fn sub_inner(&self, rhs: &Self) -> Vec<u32> {
        self.sub_inner_with_sign(rhs).0
    }
}
