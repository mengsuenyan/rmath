
use crate::bigint::BigInt;
use std::str::FromStr;

macro_rules! test_bigint_fromfmt_help {
    (($Type0: ty, $FS0: literal, $FS1: literal)) => {
        let (min, max) = (<$Type0>::MIN, <$Type0>::MAX);
        let (min_str, max_str) = (if min != 0 {format!($FS1, min)} else {format!($FS0, min)}, format!($FS0, max));
        let (min_bi, max_bi) = (BigInt::from(min), BigInt::from(max));
        assert_eq!(min_str, format!($FS0, min_bi), "case: {}{}",  min, stringify!($Type0));
        assert_eq!(max_str, format!($FS0, max_bi), "case: {}{}", max, stringify!($Type0));
        assert_eq!(min_bi, BigInt::from_str(min_str.as_str()).unwrap(), "case: {}{}", min_str, stringify!($Type0));
        assert_eq!(max_bi, BigInt::from_str(max_str.as_str()).unwrap(), "case: {}{}", max_str, stringify!($Type0));
    };
    (($Type0: ty, $FS0: literal, $FS1: literal), $(($Type1: ty, $FS10: literal, $FS11: literal)),+) => {
        test_bigint_format_help!(($Type0, $FS0, $FS1));
        test_bigint_format_help!($(($Type1, $FS10, $FS11)),+);
    };
}

macro_rules! test_bigint_fromfmt {
    ($Type0: ty) => {
        // Display
        test_bigint_fromfmt_help!(($Type0, "{}", "{}"));
        
        // Octal
        test_bigint_fromfmt_help!(($Type0, "{:#o}", "-{:#o}"));
        
        // LowerHex
        test_bigint_fromfmt_help!(($Type0, "{:#x}", "-{:#x}"));
        
        // UpperHex
        test_bigint_fromfmt_help!(($Type0, "{:#X}", "-{:#X}"));
        
        // Binary
        test_bigint_fromfmt_help!(($Type0, "{:#b}", "-{:#b}"));
        
        // Debug
        let (min, max) = (<$Type0>::MIN, <$Type0>::MAX);
        let (min_str, max_str) = (if min != 0 {format!("-{:#x}", min)} else {format!("{:#x}", min)}, format!("{:#x}", max));
        let (min_bi, max_bi) = (BigInt::from(min), BigInt::from(max));
        assert_eq!(min_str, format!("{:#?}", min_bi), "case: {}{}",  min, stringify!($Type0));
        assert_eq!(max_str, format!("{:#?}", max_bi), "case: {}{}", max, stringify!($Type0));
        assert_eq!(min_bi, BigInt::from_str(min_str.as_str()).unwrap(), "case: {}{}", min_str, stringify!($Type0));
        assert_eq!(max_bi, BigInt::from_str(max_str.as_str()).unwrap(), "case: {}{}", max_str, stringify!($Type0));
    };
    ($Type0: ty, $($Type1: ty),+) => {
        test_bigint_fromfmt!($Type0);
        test_bigint_fromfmt!($($Type1),+);
    }
}

#[test]
fn bigint_from_and_fmt() {
    test_bigint_fromfmt!(i8, i16, i32, i64, isize, i128, u8, u16, usize, u32, u64, u128);
}

#[test]
fn bigint_relation_arith() {
    let l1 = BigInt::from(std::u128::MAX);
    let l2 = BigInt::from(std::u128::MAX);
    let l_sum = BigInt::from_str("0x1fffffffffffffffffffffffffffffffe").unwrap();
    let s1 = BigInt::from(std::u8::MAX);
    let s2 = BigInt::from(std::u8::MAX);
    let s_sum = BigInt::from_str("0x1fe").unwrap();
    let nan = BigInt::nan();
    assert_eq!(l1, l2);
    assert!(l1 <= l2);
    assert!(l1 <= l_sum);
    assert!(l2 < l_sum);
    assert!(s_sum > s1);
    assert!(s_sum >= s2);
    assert_ne!(nan , nan);
    assert_ne!(l1 , nan);
    assert_ne!(nan , l1);
    assert_eq!(BigInt::from(0u8), BigInt::from(0i128));
}

#[test]
fn bigint_logical_arith() {
    let l1 = BigInt::from(std::u128::MAX);
    let l2 = BigInt::from(std::u128::MAX);

    assert_eq!(l1.clone() & l2.clone(), l1);
    assert_eq!(l1.clone() | l2.clone(), l2);
    assert_eq!(l1.clone() ^ l2.clone(), BigInt::from(0));
    assert_eq!(!l1.clone(), BigInt::from(0));
    assert_eq!(
        format!("{}", l1.clone() & BigInt::nan()),
        format!("{}", BigInt::nan())
    );
    assert_ne!(l1.clone() & BigInt::nan(), BigInt::nan());
    
    let l1 = BigInt::from_str("0xfffffffffffffffffffffffffffffffffff3222222222222222222234900000000000000ffffffffffffffffffffff").unwrap();
    let l2 = BigInt::from_str("0xff9000000000000000000000322222222222223209053065839583093285340530493058304593058390584").unwrap();
    assert_eq!(l1.clone() ^ l2.clone(), BigInt::from_str("0xfffffff006fffffffffffffffffffffcddd1000000000102b271247b7058309328534053fb6cfa7cfba6cfa7c6fa7b").unwrap());
    assert_eq!(l1.clone() | l2.clone(), BigInt::from_str("0xfffffffffffffffffffffffffffffffffff3222222222322b273267b7958309328534053ffffffffffffffffffffff").unwrap());
    assert_eq!(l1.clone() & l2.clone(), BigInt::from_str("0xff9000000000000000000000322222222222222200002020009000000000000000493058304593058390584").unwrap());
    assert_eq!(!l2.clone(), BigInt::from_str("-0x6fffffffffffffffffffffcdddddddddddddcdf6facf9a7c6a7cf6cd7acbfacfb6cfa7cfba6cfa7c6fa7b").unwrap());
    assert_eq!(!BigInt::from_str("0b11000011").unwrap(), BigInt::from_str("-0b111100").unwrap());
}

#[test]
fn bigint_shift_arith() {
    let l2 = BigInt::from_str("0xff9000000000000000000000322222222222223209053065839583093285340530493058304593058390584").unwrap();
    let l3 = BigInt::from_str("0x1ff20000000000000000000006444444444444464120a60cb072b0612650a680a609260b0608b260b0720b08").unwrap();
    assert_eq!(l2.clone() << 1, l3);
    assert_eq!(l2.clone() << 0, l2);
    assert_eq!(l2.clone() << 30, BigInt::from_str("0x3fe4000000000000000000000c8888888888888c82414c1960e560c24ca14d014c124c160c1164c160e416100000000").unwrap());
    assert_eq!(l2.clone() << 10000, BigInt::from_str("0xff90000000000000000000003222222222222232090530658395830932853405304930583045930583905840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000").unwrap());
    assert_eq!(l2.clone() >> 4, BigInt::from_str("0xff900000000000000000000032222222222222320905306583958309328534053049305830459305839058").unwrap());
    assert_eq!(l2.clone() >> 1, BigInt::from_str("0x7fc800000000000000000000191111111111111904829832c1cac18499429a029824982c1822c982c1c82c2").unwrap());
    assert_eq!(l2.clone() >> 0, l2);
    assert_eq!(l2.clone() >> 1001, BigInt::from(0));
    assert_eq!(BigInt::from(0) << 0, BigInt::from(0));
    assert_eq!(BigInt::from(0) << 3, BigInt::from(0));
}

#[test]
fn bigint_add() {
    let mut l1 = BigInt::from(std::u128::MAX);
    let l2 = BigInt::from(std::u128::MAX);
    let sum = BigInt::from_str("0x1fffffffffffffffffffffffffffffffe").unwrap();
    assert_eq!(l1.clone() + l2.clone(), sum);
    l1 += l2;
    assert_eq!(l1, sum);
    assert_eq!(
        l1 + BigInt::from(1),
        BigInt::from_str("0x1ffffffffffffffffffffffffffffffff").unwrap()
    );
    let l1 = BigInt::from_str("0xfffffffffffffffffffffffffffffffffff3222222222222222222234900000000000000ffffffffffffffffffffff").unwrap();
    let l2 = BigInt::from_str("0xff9000000000000000000000322222222222223209053065839583093285340530493058304593058390584").unwrap();
    let sum = BigInt::from_str("0x10000000ff900000000000000000000032215444444444542b275287b82583093285340540493058304593058390583").unwrap();
    assert_eq!(l1.clone() + l2.clone(), sum, "{}=====>{}======{}", l1, l2, sum);

    let s1 = BigInt::from(std::u8::MAX);
    let s2 = BigInt::from(std::u8::MAX);
    let sum = BigInt::from_str("0x1fe").unwrap();
    assert_eq!(s1 + s2, sum);

    let nan = BigInt::nan();
    assert_eq!(format!("{:x}", nan.clone() + l1), format!("{:x}", nan));
}

#[test]
fn bigint_sub() {
    let l1 = BigInt::from(std::u128::MAX);
    let l2 = BigInt::from(std::u8::MAX);
    assert_eq!(l1.clone() - l1.clone(), BigInt::from(0));
    assert_eq!(
        l1.clone() - l2.clone(),
        BigInt::from(std::u128::MAX - (std::u8::MAX as u128))
    );
    assert_eq!(l2.clone() - l1.clone(), -(l1.clone() - l2.clone()));
    let l1 = BigInt::from_str("0xfffffffffffffffffffffffffffffffffff3222222222222222222234900000000000000ffffffffffffffffffffff").unwrap();
    let l2 = BigInt::from_str("0x32888f300000000000000322222229750348593045830670204").unwrap();
    let sub = BigInt::from_str("0xfffffffffffffffffffffffffffffffffff32222221ef9992f22222348ffffffcdddddde68afcb7a6cfba7cf98fdfb").unwrap();
    assert_eq!(l1.clone() - l2.clone(), sub);
    assert_eq!(l2 - l1, -sub);
}

#[test]
fn bigint_mul() {
    let l1 = BigInt::from(10);
    assert_eq!(l1.clone() * l1.clone(), BigInt::from(100));
    assert_eq!(l1.clone() * BigInt::from(0), BigInt::from(0));
    assert_eq!(l1.clone() * BigInt::from(1), l1);
    let l1 = BigInt::from_str("0xf9058301048250fabddeabf9320480284932084552541").unwrap();
    let l2 = BigInt::from_str("0xf329053910428502fabcd9230494035242429890eacb").unwrap();
    let m = BigInt::from_str("0xec882250900ba90c2088a4a5ee549ecc5152d7a50683a82daa24e03f6d6409468abf1ce1f01d9be845021f48b").unwrap();
    assert_eq!(l1.clone() * l2.clone(), m);
}


#[test]
fn test_div() {
    let l1 = BigInt::from(100);
    let l2 = BigInt::from(10);
    assert_eq!(l1.clone() / l2.clone(), BigInt::from(10));
    let l1 = BigInt::from_str("0xfffffffffff32908329058205820").unwrap();
    let l2 = BigInt::from_str("0xff").unwrap();
    let quo = BigInt::from_str("0x10101010100f41d2557e84060b8").unwrap();
    assert_eq!(l1.clone() / l2.clone(), quo);
    assert_eq!(l2.clone() / l1.clone(), BigInt::from(0));
    let l1 = BigInt::from_str("0x39025820857032850384502853503850325fa3242de121").unwrap();
    let l2 = BigInt::from_str("0x2048537058358afedead392582075275").unwrap();
    let quo = BigInt::from_str("0x1c414f70ec1f027").unwrap();
    assert_eq!(l1.clone() / l2.clone(), quo);
    let l1 = BigInt::from(0x1ad7f29abcau128);
    assert_eq!(l1.clone() / BigInt::from(10), BigInt::from(184467440737u128));
}

#[test]
fn bigint_rem() {
    let l1 = BigInt::from_str("0xffffffffffffff000000000000").unwrap();
    let l2 = BigInt::from(255u8);
    assert_eq!(l1.clone() % l2.clone(), BigInt::from(0));
    let l1 = BigInt::from_str("0x39025820857032850384502853503850325fa3242de121").unwrap();
    let l2 = BigInt::from_str("0x2048537058358afedead392582075275").unwrap();
    let rem = BigInt::from_str("0xab9de6183b632a33dc2601ae78da14e").unwrap();
    assert_eq!(l1.clone() % l2.clone(), rem);
    let l1 = BigInt::from_str("0xfffffffffff32908329058205820").unwrap();
    let l2 = BigInt::from_str("0xff").unwrap();
    let quo = BigInt::from_str("0xd8").unwrap();
    assert_eq!(l1.clone() % l2.clone(), quo);
}

#[test]
fn bigint_gcd() {
    // the test cases come from the int_test.go in the golang source code
    // 0  1  2  3  4
    // d, x, y, a, b
    let cases = [
        ("0", "0", "0", "0", "0"),
        ("7", "0", "1", "0", "7"),
        ("7", "0", "-1", "0", "-7"),
        ("11", "1", "0", "11", "0"),
        ("7", "-1", "-2", "-77", "35"),
        ("935", "-3", "8", "64515", "24310"),
        ("935", "-3", "-8", "64515", "-24310"),
        ("935", "3", "-8", "-64515", "-24310"),

        ("1", "-9", "47", "120", "23"),
        ("7", "1", "-2", "77", "35"),
        ("935", "-3", "8", "64515", "24310"),
        ("935000000000000000", "-3", "8", "64515000000000000000", "24310000000000000000"),
        ("1", "-221", "22059940471369027483332068679400581064239780177629666810348940098015901108344", "98920366548084643601728869055592650835572950932266967461790948584315647051443", "991"),
    ];

    for ele in cases.iter() {
        let a = BigInt::from_str(ele.3).unwrap();
        let b = BigInt::from_str(ele.4).unwrap();
        let (d, x, y) = a.gcd(b);

        assert_eq!(d, BigInt::from_str(ele.0).unwrap());
        assert_eq!(x, BigInt::from_str(ele.1).unwrap());
        assert_eq!(y, BigInt::from_str(ele.2).unwrap());
    }
}


#[test]
fn bigint_mod_inverse() {
    // the test cases come from the int_test.go in the golang source code
    let cases = [
        ("1234567", "458948883992"),
        ("239487239847", "2410312426921032588552076022197566074856950548502459942654116941958108831682612228890093858261341614673227141477904012196503648957050582631942730706805009223062734745341073406696246014589361659774041027169249453200378729434170325843778659198143763193776859869524088940195577346119843545301547043747207749969763750084308926339295559968882457872412993810129130294592999947926365264059284647209730384947211681434464714438488520940127459844288859336526896320919633919"),
        ("-10", "13"), // issue #16984
        ("10", "-13"),
        ("-17", "-13"),
    ];

    for ele in cases.iter() {
        let g = BigInt::from_str(ele.0).unwrap();
        let n = BigInt::from_str(ele.1).unwrap();
        let inv = g.mod_inverse(n.clone());
        let inv_g = g * inv;
        let inv = inv_g.mod_inverse(n);
        assert_eq!(inv, BigInt::from(1));
    }
}

#[test]
fn bigint_solve_mod_linear_equation() {
    // (a,b,n)
    let cases = [
        (("14", "30", "100"), vec!["0x2d", "0x5f"]),
        (("1234567","1", "458948883992"), vec!["0x3564cd46f"]),
         (("239487239847","1", 
           "2410312426921032588552076022197566074856950548502459942654116941958108831682612228890093858261341614673227141477904012196503648957050582631942730706805009223062734745341073406696246014589361659774041027169249453200378729434170325843778659198143763193776859869524088940195577346119843545301547043747207749969763750084308926339295559968882457872412993810129130294592999947926365264059284647209730384947211681434464714438488520940127459844288859336526896320919633919"), 
          vec!["0x698588a50632e78c394b1bfd6a8193de984a09ae10c0be7d9ab21c657565b2b958367aaa0f629bc02d9fd18665f92d04280f07da8ef40bd6b4752bc556624c1104404fbc0cf771c365869d97a39fbd54a2b0b652f73239060c8b11bbe47673f5d169ab9ea745cdc2245cdbd0932b67c8dd4bb23e1430f98626664388ad33d8507e99584f15dc541cecb09f9594384b244abc69dd76f792ba3c1ac0e2deff6a9324f17b5f71fa4176084ad6101864074dde492221c6991d3132efc745814e4c8c"]),
        (("-10","1", "13"), vec!["0x9"]), // issue #16984
        (("10","1", "-13"), vec!["0x4"]),
         (("-17","1", "-13"), vec!["0x3"]),
    ];
    
    cases.iter().for_each(|(equa, res)| {
        let a: BigInt = equa.0.parse().unwrap();
        let b: BigInt = equa.1.parse().unwrap();
        let n: BigInt = equa.2.parse().unwrap();
        let mut x = a.solve_mod_linear_equation(b, n).unwrap();
        x.sort_by(|a, b| {
            a.partial_cmp(b).unwrap()
        });
        let (mut left, mut right) = (Vec::new(), Vec::new());
        x.iter().for_each(|e| {left.push(format!("{:#x}", e));});
        res.iter().for_each(|e| {right.push(e.to_string());});
        assert_eq!(left, right, "case: {}", equa.0);
    });
}
