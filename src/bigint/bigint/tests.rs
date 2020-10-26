
use crate::bigint::{BigInt};
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

#[test]
fn bigint_mul_range() {
    let cases = [
        (-1i64, 1i64, "0"),
        (-2, -1, "2"),
        (-3, -2, "6"),
        (-3, -1, "-6"),
        (1, 3, "6"),
        (-10, -10, "-10"),
        (0, -1, "1"),
        (-1, -100, "1"),
        (-1, 1, "0"),
        (-1000_000_000, 0, "0"),
        (-1000_000_000, 1000_000_000, "0"),
        (-10, -1, "3628800"),
        (-20, -2, "-2432902008176640000"),
        (-99, -1,
            "-933262154439441526816992388562667004907159682643816214685929638952175999932299156089414639761565182862536979208272237582511852109168640000000000000000000000",
        ),
    ];
    
    cases.iter().for_each(|e| {
        let res: BigInt = e.2.parse().unwrap();
        let m = BigInt::mul_range(e.0, e.1);
        assert_eq!(m, res, "case: mul_range({}, {})", e.0, e.1);
    });
}

#[test]
fn bigint_binomial() {
    let cases = [
        (0, 0, "1"),
        (0, 1, "0"),
        (1, 0, "1"),
        (1, 1, "1"),
        (1, 10, "0"),
        (4, 0, "1"),
        (4, 1, "4"),
        (4, 2, "6"),
        (4, 3, "4"),
        (4, 4, "1"),
        (10, 1, "10"),
        (10, 9, "10"),
        (10, 5, "252"),
        (11, 5, "462"),
        (11, 6, "462"),
        (100, 10, "17310309456440"),
        (100, 90, "17310309456440"),
        (1000, 10, "263409560461970212832400"),
        (1000, 990, "263409560461970212832400"),
    ];
    
    cases.iter().for_each(|e| {
        let res: BigInt = e.2.parse().unwrap();
        let m = BigInt::binomial(e.0, e.1);
        assert_eq!(m, res, "case: binomial({}, {})", e.0, e.1);
    });
}

#[test]
fn bigint_exp() {
    // (x, y, m, out)
    let cases = [
        // y <= 0
        ("0", "0", "0", "1"),
        ("1", "0", "0", "1"),
        ("-10", "0", "0", "1"),
        ("1234", "-1", "0", "1"),
        ("1234", "-1", "0", "1"),
        ("17", "-100", "1234", "865"),
        ("2", "-100", "1234", "1"),
        
        // m == 1
        ("0", "0", "1", "0"),
        ("1", "0", "1", "0"),
        ("-10", "0", "1", "0"),
        ("1234", "-1", "1", "0"),
        
        // misc
        ("5", "1", "3", "2"),
        ("5", "-7", "0", "1"),
        ("-5", "-7", "0", "1"),
        ("5", "0", "0", "1"),
        ("-5", "0", "0", "1"),
        ("5", "1", "0", "5"),
        ("-5", "1", "0", "-5"),
        ("-5", "1", "7", "2"),
        ("-2", "3", "2", "0"),
        ("5", "2", "0", "25"),
        ("1", "65537", "2", "1"),
        ("0x8000000000000000", "2", "0", "0x40000000000000000000000000000000"),
        ("0x8000000000000000", "2", "6719", "4944"),
        ("0x8000000000000000", "3", "6719", "5447"),
        ("0x8000000000000000", "1000", "6719", "1603"),
        ("0x8000000000000000", "1000000", "6719", "3199"),
        ("0x8000000000000000", "-1000000", "6719", "3663"), // 3663 = ModInverse(3199, 6719) Issue #25865
        
        ("0xffffffffffffffffffffffffffffffff", "0x12345678123456781234567812345678123456789", "0x01112222333344445555666677778889", "0x36168FA1DB3AAE6C8CE647E137F97A"),
        
        (
            "2938462938472983472983659726349017249287491026512746239764525612965293865296239471239874193284792387498274256129746192347",
            "298472983472983471903246121093472394872319615612417471234712061",
            "29834729834729834729347290846729561262544958723956495615629569234729836259263598127342374289365912465901365498236492183464",
            "23537740700184054162508175125554701713153216681790245129157191391322321508055833908509185839069455749219131480588829346291",
        ),
        // test case for issue 8822
        (
            "11001289118363089646017359372117963499250546375269047542777928006103246876688756735760905680604646624353196869572752623285140408755420374049317646428185270079555372763503115646054602867593662923894140940837479507194934267532831694565516466765025434902348314525627418515646588160955862839022051353653052947073136084780742729727874803457643848197499548297570026926927502505634297079527299004267769780768565695459945235586892627059178884998772989397505061206395455591503771677500931269477503508150175717121828518985901959919560700853226255420793148986854391552859459511723547532575574664944815966793196961286234040892865",
            "0xB08FFB20760FFED58FADA86DFEF71AD72AA0FA763219618FE022C197E54708BB1191C66470250FCE8879487507CEE41381CA4D932F81C2B3F1AB20B539D50DCD",
            "0xAC6BDB41324A9A9BF166DE5E1389582FAF72B6651987EE07FC3192943DB56050A37329CBB4A099ED8193E0757767A13DD52312AB4B03310DCD7F48A9DA04FD50E8083969EDB767B0CF6095179A163AB3661A05FBD5FAAAE82918A9962F0B93B855F97993EC975EEAA80D740ADBF4FF747359D041D5C33EA71D281E446B14773BCA97B43A23FB801676BD207A436C6481F1D2B9078717461A5B9D32E688F87748544523B524B0D57D5EA77A2775D2ECFA032CFBDBF52FB3786160279004E57AE6AF874E7303CE53299CCC041C7BC308D82A5698F3A8D0C38271AE35F8E9DBFBB694B5C803D89F7AE435DE236D525F54759B65E372FCD68EF20FA7111F9E4AFF73",
            "21484252197776302499639938883777710321993113097987201050501182909581359357618579566746556372589385361683610524730509041328855066514963385522570894839035884713051640171474186548713546686476761306436434146475140156284389181808675016576845833340494848283681088886584219750554408060556769486628029028720727393293111678826356480455433909233520504112074401376133077150471237549474149190242010469539006449596611576612573955754349042329130631128234637924786466585703488460540228477440853493392086251021228087076124706778899179648655221663765993962724699135217212118535057766739392069738618682722216712319320435674779146070442",
        ),
        (
            "-0x1BCE04427D8032319A89E5C4136456671AC620883F2C4139E57F91307C485AD2D6204F4F87A58262652DB5DBBAC72B0613E51B835E7153BEC6068F5C8D696B74DBD18FEC316AEF73985CF0475663208EB46B4F17DD9DA55367B03323E5491A70997B90C059FB34809E6EE55BCFBD5F2F52233BFE62E6AA9E4E26A1D4C2439883D14F2633D55D8AA66A1ACD5595E778AC3A280517F1157989E70C1A437B849F1877B779CC3CDDEDE2DAA6594A6C66D181A00A5F777EE60596D8773998F6E988DEAE4CCA60E4DDCF9590543C89F74F603259FCAD71660D30294FBBE6490300F78A9D63FA660DC9417B8B9DDA28BEB3977B621B988E23D4D954F322C3540541BC649ABD504C50FADFD9F0987D58A2BF689313A285E773FF02899A6EF887D1D4A0D2",
            "0xB08FFB20760FFED58FADA86DFEF71AD72AA0FA763219618FE022C197E54708BB1191C66470250FCE8879487507CEE41381CA4D932F81C2B3F1AB20B539D50DCD",
            "0xAC6BDB41324A9A9BF166DE5E1389582FAF72B6651987EE07FC3192943DB56050A37329CBB4A099ED8193E0757767A13DD52312AB4B03310DCD7F48A9DA04FD50E8083969EDB767B0CF6095179A163AB3661A05FBD5FAAAE82918A9962F0B93B855F97993EC975EEAA80D740ADBF4FF747359D041D5C33EA71D281E446B14773BCA97B43A23FB801676BD207A436C6481F1D2B9078717461A5B9D32E688F87748544523B524B0D57D5EA77A2775D2ECFA032CFBDBF52FB3786160279004E57AE6AF874E7303CE53299CCC041C7BC308D82A5698F3A8D0C38271AE35F8E9DBFBB694B5C803D89F7AE435DE236D525F54759B65E372FCD68EF20FA7111F9E4AFF73",
            "21484252197776302499639938883777710321993113097987201050501182909581359357618579566746556372589385361683610524730509041328855066514963385522570894839035884713051640171474186548713546686476761306436434146475140156284389181808675016576845833340494848283681088886584219750554408060556769486628029028720727393293111678826356480455433909233520504112074401376133077150471237549474149190242010469539006449596611576612573955754349042329130631128234637924786466585703488460540228477440853493392086251021228087076124706778899179648655221663765993962724699135217212118535057766739392069738618682722216712319320435674779146070442",
        ),
        
        // test cases for issue 13907
        ("0xffffffff00000001", "0xffffffff00000001", "0xffffffff00000001", "0"),
        ("0xffffffffffffffff00000001", "0xffffffffffffffff00000001", "0xffffffffffffffff00000001", "0"),
        ("0xffffffffffffffffffffffff00000001", "0xffffffffffffffffffffffff00000001", "0xffffffffffffffffffffffff00000001", "0"),
        ("0xffffffffffffffffffffffffffffffff00000001", "0xffffffffffffffffffffffffffffffff00000001", "0xffffffffffffffffffffffffffffffff00000001", "0"),
        
        (
            "2",
            "0xB08FFB20760FFED58FADA86DFEF71AD72AA0FA763219618FE022C197E54708BB1191C66470250FCE8879487507CEE41381CA4D932F81C2B3F1AB20B539D50DCD",
            "0xAC6BDB41324A9A9BF166DE5E1389582FAF72B6651987EE07FC3192943DB56050A37329CBB4A099ED8193E0757767A13DD52312AB4B03310DCD7F48A9DA04FD50E8083969EDB767B0CF6095179A163AB3661A05FBD5FAAAE82918A9962F0B93B855F97993EC975EEAA80D740ADBF4FF747359D041D5C33EA71D281E446B14773BCA97B43A23FB801676BD207A436C6481F1D2B9078717461A5B9D32E688F87748544523B524B0D57D5EA77A2775D2ECFA032CFBDBF52FB3786160279004E57AE6AF874E7303CE53299CCC041C7BC308D82A5698F3A8D0C38271AE35F8E9DBFBB694B5C803D89F7AE435DE236D525F54759B65E372FCD68EF20FA7111F9E4AFF73", // odd
            "0x6AADD3E3E424D5B713FCAA8D8945B1E055166132038C57BBD2D51C833F0C5EA2007A2324CE514F8E8C2F008A2F36F44005A4039CB55830986F734C93DAF0EB4BAB54A6A8C7081864F44346E9BC6F0A3EB9F2C0146A00C6A05187D0C101E1F2D038CDB70CB5E9E05A2D188AB6CBB46286624D4415E7D4DBFAD3BCC6009D915C406EED38F468B940F41E6BEDC0430DD78E6F19A7DA3A27498A4181E24D738B0072D8F6ADB8C9809A5B033A09785814FD9919F6EF9F83EEA519BEC593855C4C10CBEEC582D4AE0792158823B0275E6AEC35242740468FAF3D5C60FD1E376362B6322F78B7ED0CA1C5BBCD2B49734A56C0967A1D01A100932C837B91D592CE08ABFF",
        ),
        // 这个测试实例golang计算错误, 64位系统下, expNNWindowed中i=7, j=12轮中的第三个div求模运算错误
        (
            "2",
            "0xB08FFB20760FFED58FADA86DFEF71AD72AA0FA763219618FE022C197E54708BB1191C66470250FCE8879487507CEE41381CA4D932F81C2B3F1AB20B539D50DCD",
            "0xAC6BDB41324A9A9BF166DE5E1389582FAF72B6651987EE07FC3192943DB56050A37329CBB4A099ED8193E0757767A13DD52312AB4B03310DCD7F48A9DA04FD50E8083969EDB767B0CF6095179A163AB3661A05FBD5FAAAE82918A9962F0B93B855F97993EC975EEAA80D740ADBF4FF747359D041D5C33EA71D281E446B14773BCA97B43A23FB801676BD207A436C6481F1D2B9078717461A5B9D32E688F87748544523B524B0D57D5EA77A2775D2ECFA032CFBDBF52FB3786160279004E57AE6AF874E7303CE53299CCC041C7BC308D82A5698F3A8D0C38271AE35F8E9DBFBB694B5C803D89F7AE435DE236D525F54759B65E372FCD68EF20FA7111F9E4AFF72", // even
            // "0x7858794B5897C29F4ED0B40913416AB6C48588484E6A45F2ED3E26C941D878E923575AAC434EE2750E6439A6976F9BB4D64CEDB2A53CE8D04DD48CADCDF8E46F22747C6B81C6CEA86C0D873FBF7CEF262BAAC43A522BD7F32F3CDAC52B9337C77B3DCFB3DB3EDD80476331E82F4B1DF8EFDC1220C92656DFC9197BDC1877804E28D928A2A284B8DED506CBA304435C9D0133C246C98A7D890D1DE60CBC53A024361DA83A9B8775019083D22AC6820ED7C3C68F8E801DD4EC779EE0A05C6EB682EF9840D285B838369BA7E148FA27691D524FAEAF7C6ECE2A4B99A294B9F2C241857B5B90CC8BFFCFCF18DFA7D676131D5CD3855A5A3E8EBFA0CDFADB4D198B4A",
            "0x89b0f1232613acbdb3fc4e8f2d600b8e2ba0ff28419c21eb2c747806911a407b84904206e234d2a0227d6d40475fb46f425d92b392767ee2c970306327717997ed7a9bd3f3a5483396490bd6bd71fd9122b549774ef53220cd7b6f462538ccbd1ee50b5e6e3c418960eb45d5ea328e7ffc66fe5d138065cf371d63f0f13df118e689bc6235c438575c8a39f2a7d8d1e447e7e075f34b0bbea7c60422e30c251ba064db01a5872521455bf33f226f6dea8e02bcb7c5690fba390c67fddcf3dc321d576755c50c217aff32182819b30b77e44ff6f2279cdcaf020aca165bd396695016648b4e492bb1f41188691a9c1b1d059e090b9cfb8b21a08889f9e93a81c6",
        ),
    ];
    
    cases.iter().for_each(|e| {
        let out = BigInt::from_str(e.3).unwrap();
        let x = BigInt::from_str(e.0).unwrap();
        let y = BigInt::from_str(e.1).unwrap();
        let m = BigInt::from_str(e.2).unwrap();
        let exp = x.exp(&y, &m);
        assert_eq!(exp, out, "case: {}^{} mod {}", e.0, e.1, e.2);
    });
}

#[test]
fn bigint_jacobi() {
    // (x,y,out)
    let cases = [
        (0, 1, 1),
        (0, -1, 1),
        (1, 1, 1),
        (1, -1, 1),
        (0, 5, 0),
        (1, 5, 1),
        (2, 5, -1),
        (-2, 5, -1),
        (2, -5, -1),
        (-2, -5, 1),
        (3, 5, -1),
        (5, 5, 0),
        (-5, 5, 0),
        (6, 5, 1),
        (6, -5, 1),
        (-6, 5, 1),
        (-6, -5, -1),
    ];
    
    cases.iter().for_each(|e| {
        let x = BigInt::from(e.0);
        let y = BigInt::from(e.1);
        let out = Some(e.2);
        let j = x.jacobi(&y);
        assert_eq!(j, out, "case: jacobi({}, {})", x, y);
    });
}