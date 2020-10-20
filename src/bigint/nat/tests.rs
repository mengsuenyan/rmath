use std::mem;
use super::*;
use crate::rand::{DefaultSeed, CryptoRand};
use std::time::Instant;

macro_rules! test_nat_from {
    (($type0: ty, $step: literal)) => {
        if mem::size_of::<$type0>() <= mem::size_of::<usize>() {
            let x = (<$type0>::MAX / $step) as usize;
            (0..=<$type0>::MAX).step_by(x).for_each(|e| {
                assert_eq!(Nat::from(e), e, "Nat::from({}{})", e, stringify!($type0));
                let s = format!("{:#x}", e);
                assert_eq!(format!("{:#x}", Nat::from_str(s.as_str()).unwrap()), s, "Nat::from_str(\"{}\")", s);
                let s = format!("{:#b}", e);
                assert_eq!(format!("{:#b}", Nat::from_str(s.as_str()).unwrap()), s, "Nat::from_str(\"{}\")", s);
                let s = format!("{:#o}", e);
                assert_eq!(format!("{:#o}", Nat::from_str(s.as_str()).unwrap()), s, "Nat::from_str(\"{}\")", s);
                // let s = format!("{}", e);
                // assert_eq!(Nat::from_str(s.as_str()).unwrap(), Nat::from(e), "Nat::from_str(\"{}\"", s);
            });
        } else {
            let mut i = 0 as $type0;
            let x = <$type0>::MAX / ($step as $type0);
            while i <= <$type0>::MAX {
                assert_eq!(Nat::from(i), i, "Nat::from({}{})", i, stringify!($type0));
                
                let s = format!("{:#x}", i);
                assert_eq!(format!("{:#x}", Nat::from_str(s.as_str()).unwrap()), s, "Nat::from_str(\"{}\")", s);
                let s = format!("{:#b}", i);
                assert_eq!(format!("{:#b}", Nat::from_str(s.as_str()).unwrap()), s, "Nat::from_str(\"{}\")", s);
                let s = format!("{:#o}", i);
                assert_eq!(format!("{:#o}", Nat::from_str(s.as_str()).unwrap()), s, "Nat::from_str(\"{}\")", s);
                
                i += x;
                let (a, c) = i.overflowing_add(x);
                if c {break;}
                i = a;
            }
        }
    };
    (($type0: ty, $step: literal), $(($type1: ty, $step1: literal)),+) => {
        test_nat_from!(($type0, $step));
        test_nat_from!($(($type1, $step1)),+);
    }
}

#[test]
fn nat_from_and_fmt() {
    test_nat_from!(
        (u128, 5),
        (u64, 5),
        (usize, 5),
        (u32, 5),
        (u16, 5),
        (u8, 5)
    );
    
    let cases = [
        (vec![0x32905332, 0xffccddaa, 0x00000000, 0x00bb0032, 0x11111111, 0x01101039, 0x12345678, 0x87654321, 0x0000]),
        (vec![u32::MAX, u32::MAX, u32::MAX, u32::MAX, u32::MAX, u32::MAX, u32::MAX]),
        (vec![0,0,0,0,0,0,0]),
        (vec![0x32u32, 0x54, 0x87, 0x90, 0xaf, 0x7b, 0x4c, 0xdd]),
        (vec![0]),
        (vec![111]),
        (vec![]),
    ];
    
    cases.iter().for_each(|x| {
        let s: String = x.iter().rev().map(|&x| {format!("{:08x}", x)}).collect::<Vec<String>>().join("");
        let mut s = s.trim_start_matches('0').to_string();
        
        if s.is_empty() {
            s.push_str(if x.is_empty() {"NaN"} else {"0"});
        }
        
        let nat_x = Nat::from(x);
        assert_eq!(format!("{:x}", nat_x), s, "Nat::from({})", s);
        
        let mut y = Vec::with_capacity(x.len() << 2);
        x.iter().for_each(|&ele| {y.extend_from_slice(ele.to_le_bytes().as_ref());});
        while y.last() == Some(&0) {
            y.pop();
        }
        if y.is_empty() && !x.is_empty() {y.push(0);}
        let nat_y = Nat::from(y);
        assert_eq!(format!("{:x}", nat_y), s, "Nat::from({:?})", s);
        
        let hs = format!("0x{}", s);
        if x.is_empty() {
            assert!(Nat::from_str(hs.as_str()).is_err(), "NaN");
        } else {
            assert_eq!(Nat::from_str(hs.as_str()).unwrap(), nat_x, "Nat::from_str(\"{}\")", hs);
            let hs = format!("{:#X}", nat_y);
            assert_eq!(Nat::from_str(hs.as_str()).unwrap(), nat_x, "Nat::from_str(\"{}\")", hs);
            let hs = format!("{:#b}", nat_y);
            assert_eq!(Nat::from_str(hs.as_str()).unwrap(), nat_x, "Nat::from_str(\"{}\")", hs);
            let hs = format!("{:#o}", nat_y);
            assert_eq!(Nat::from_str(hs.as_str()).unwrap(), nat_x, "Nat::from_str(\"{}\")", hs);
        }
    });
}

#[test]
fn nat_cmp() {
    let l1 = Nat::from(std::u128::MAX);
    let l2 = Nat::from(std::u128::MAX);
    let l_sum = Nat::from_str("0x1fffffffffffffffffffffffffffffffe").unwrap();
    let s1 = Nat::from(std::u8::MAX);
    let s2 = Nat::from(std::u8::MAX);
    let s_sum = Nat::from_str("0x1fe").unwrap();
    let nan = Nat::from(Vec::<u32>::new());
    assert_eq!(l1, l2);
    assert!(l1 <= l2);
    assert!(l1 <= l_sum);
    assert!(l2 < l_sum);
    assert!(s_sum > s1);
    assert!(s_sum >= s2);
    assert_ne!(nan, nan);
    assert_ne!(l1 , nan);
    assert_ne!(nan , l1);
    assert_eq!(Nat::from(0u8), Nat::from(0u128));
}

#[test]
fn nat_logical() {
    let l1 = Nat::from(std::u128::MAX);
    let l2 = Nat::from(std::u128::MAX);

    assert_eq!(l1.clone() & l2.clone(), l1);
    assert_eq!(l1.clone() | l2.clone(), l2);
    assert_eq!(l1.clone() ^ l2.clone(), Nat::from(0u32));
    assert_eq!(!l1.clone(), Nat::from(0u128));
    assert_eq!(format!("{}", l1.clone() & Nat::from(Vec::<u32>::new())), format!("{}", Nat::from(Vec::<u32>::new())));

    let l1 = "0xfffffffffffffffffffffffffffffffffff3222222222222222222234900000000000000ffffffffffffffffffffff".parse::<Nat>().unwrap();
    let l2 = "0xff9000000000000000000000322222222222223209053065839583093285340530493058304593058390584".parse::<Nat>().unwrap();
    assert_eq!(l1.clone() ^ l2.clone(), Nat::from_str("0xfffffff006fffffffffffffffffffffcddd1000000000102b271247b7058309328534053fb6cfa7cfba6cfa7c6fa7b").unwrap());
    assert_eq!(l1.clone() | l2.clone(), Nat::from_str("0xfffffffffffffffffffffffffffffffffff3222222222322b273267b7958309328534053ffffffffffffffffffffff").unwrap());
    assert_eq!(l1.clone() & l2.clone(), Nat::from_str("0xff9000000000000000000000322222222222222200002020009000000000000000493058304593058390584").unwrap());
    assert_eq!(!l2.clone(), Nat::from_str("0x6fffffffffffffffffffffcdddddddddddddcdf6facf9a7c6a7cf6cd7acbfacfb6cfa7cfba6cfa7c6fa7b").unwrap());
    assert_eq!(!Nat::from_str("0b11000011").unwrap(), Nat::from_str("0b111100").unwrap());
}

#[test]
fn nat_shift() {
    assert_eq!(Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap() << 1,
               Nat::from_str("0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe").unwrap());
    let l2 = Nat::from_str("0xff9000000000000000000000322222222222223209053065839583093285340530493058304593058390584").unwrap();
    let l3 = Nat::from_str("0x1ff20000000000000000000006444444444444464120a60cb072b0612650a680a609260b0608b260b0720b08").unwrap();
    assert_eq!(l2.clone() << 0, l2.clone());
    assert_eq!(l2.clone() << 1, l3.clone());
    let l4 = Nat::from_str("0x3fe4000000000000000000000c8888888888888c82414c1960e560c24ca14d014c124c160c1164c160e416100000000").unwrap();
    assert_eq!(l2.clone() << 30, l4);
    assert_eq!(l2.clone() << 10000, Nat::from_str("0xff90000000000000000000003222222222222232090530658395830932853405304930583045930583905840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000").unwrap());
    assert_eq!(l2.clone() >> 4, Nat::from_str("0xff900000000000000000000032222222222222320905306583958309328534053049305830459305839058").unwrap());
    assert_eq!(l2.clone() >> 1, Nat::from_str("0x7fc800000000000000000000191111111111111904829832c1cac18499429a029824982c1822c982c1c82c2").unwrap());
    assert_eq!(l2.clone() >> 0, l2.clone());
    assert_eq!(l2.clone() >> 1001, Nat::from(0u8));
    assert_eq!(l4 >> 30, l2.clone());
    assert_eq!(Nat::from(0u8) << 0, Nat::from(0u8));
    assert_eq!(Nat::from(0u8) << 3, Nat::from(0u8));
}

#[test]
fn nat_sub() {
    let l1 = Nat::from(std::u128::MAX);
    let l2 = Nat::from(std::u8::MAX);
    assert_eq!(l1.clone() - l1.clone(), Nat::from(0u32));
    // assert_eq!(l1.clone() - 255u32, &l1 - &l2);
    assert_eq!(
        l1.clone() - l2.clone(),
        Nat::from(std::u128::MAX - (std::u8::MAX as u128))
    );
    assert_eq!(l2.clone() - l1.clone(), l1.clone() - l2.clone());
    let l1 = Nat::from_str("0xfffffffffffffffffffffffffffffffffff3222222222222222222234900000000000000ffffffffffffffffffffff").unwrap();
    let l2 = Nat::from_str("0x32888f300000000000000322222229750348593045830670204").unwrap();
    let sub = Nat::from_str("0xfffffffffffffffffffffffffffffffffff32222221ef9992f22222348ffffffcdddddde68afcb7a6cfba7cf98fdfb").unwrap();
    assert_eq!(l1.clone() - l2.clone(), sub);
    assert_eq!(l2.clone() - l1.clone(), sub);
    let l1 = Nat::from_str("0x32f3289577420805237534573").unwrap();
    let l2 = Nat::from(u32::max_value());
    assert_eq!(l1.clone() - l2.clone(), l1.clone() - u32::max_value());
}

#[test]
fn nat_add() {
    let mut l1 = Nat::from(std::u128::MAX);
    let l2 = Nat::from(std::u128::MAX);
    let sum = Nat::from_str("0x1fffffffffffffffffffffffffffffffe").unwrap();
    assert_eq!(l1.clone() + l2.clone(), sum);
    l1 += l2.clone();
    assert_eq!(l1, sum);
    assert_eq!(
        l1.clone() + Nat::from(1u32),
        Nat::from_str("0x1ffffffffffffffffffffffffffffffff").unwrap()
    );
    assert_eq!(
        l1.clone() + 1u32,
        Nat::from_str("0x1ffffffffffffffffffffffffffffffff").unwrap()
    );
    let l1 = Nat::from_str("0xfffffffffffffffffffffffffffffffffff3222222222222222222234900000000000000ffffffffffffffffffffff").unwrap();
    let l2 = Nat::from_str("0xff9000000000000000000000322222222222223209053065839583093285340530493058304593058390584").unwrap();
    let sum = Nat::from_str("0x10000000ff900000000000000000000032215444444444542b275287b82583093285340540493058304593058390583").unwrap();
    assert_eq!(l1.clone() + l2.clone(), sum, "{}=====>{}======{}", l1, l2, sum);

    let s1 = Nat::from(std::u8::MAX);
    let s2 = Nat::from(std::u8::MAX);
    let sum = Nat::from_str("0x1fe").unwrap();
    assert_eq!(s1.clone() + s2.clone(), sum);
    assert_eq!(s1.clone() + (u8::MAX as u32), sum);

    let nan = Nat::from(Vec::<u32>::new());
    assert_eq!(format!("{:x}", nan.clone() + l1.clone()), format!("{:x}", nan));
}

#[test]
fn nat_mul() {
    assert_eq!(Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap() *
                   Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap(),
               Nat::from_str("0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeff0000000000000000000000000000000000000000000000000000000000000001").unwrap());
    assert_eq!(Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap() *
                   Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap(),
               Nat::from_str("0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000001").unwrap());
    assert_eq!(Nat::from_str("0x123507af44107cfc63175d6cc354e6093bfeb7b0f5145641a0bc284bf1784696cc9791b18ab54de0114f6581d68041b66c7db").unwrap() *
            Nat::from_str("0xb9bd7d543685789d57cb918e833af352559021483cdb05cc21fd").unwrap(),
            Nat::from_str("0xd35cc9e369cf1fd0f297f4cf7ad21a1d9d65d9b421b51d5b689b0a47485a2c1582963dfc988179047a98dd36d5644070a0f8bb94fff1e6efeacc8ba03758fe7c8c574c12cfa377bedddabe6f").unwrap());
    assert_eq!(Nat::from_str("2938462938472983472983659726349017249287491026512746239764525612965293865296239471239874193284792387498274256129746192347").unwrap() *
                   Nat::from_str("298472983472983471903246121093472394872319615612417471234712061").unwrap(),
               Nat::from_str("877051800070821244789099242710450134536982682006837233541161511456161001386576641869116186901815671895415144768179824202865342118174193449288433467901275304066981993483906649666797167").unwrap());
    let l1 = Nat::from(10u8);
    assert_eq!(l1.clone() * l1.clone(), Nat::from(100u8));
    assert_eq!(l1.clone() * Nat::from(0u8), Nat::from(0u8));
    assert_eq!(l1.clone() * Nat::from(1u8), l1);
    assert_eq!(Nat::from(0xffffffu64) * Nat::from(0xfffffffffu128), Nat::from(0xfffffefff000001u128));
    let l1 = Nat::from_str("0xf9058301048250fabddeabf9320480284932084552541").unwrap();
    let l2 = Nat::from_str("0xf329053910428502fabcd9230494035242429890eacb").unwrap();
    let m = Nat::from_str("0xec882250900ba90c2088a4a5ee549ecc5152d7a50683a82daa24e03f6d6409468abf1ce1f01d9be845021f48b").unwrap();
    assert_eq!(l1 * l2, m);
    assert_eq!(Nat::from(u128::MAX) * Nat::from(u32::MAX), Nat::from(u128::MAX) * u32::MAX);
    assert_eq!(Nat::from(u128::MAX / 5) * Nat::from(u32::MAX), Nat::from(u128::MAX / 5) * u32::MAX);
    let l = Nat::from_str("0x123507af44107cfc63175d6cc354e6093bfeb7b0f5145641a0bc284bf1784696cc9791b18ab54de0114f6581d68041b66c7db").unwrap();
    assert_eq!( l.clone() * Nat::from(u32::MAX), l.clone() * u32::MAX);
    assert_eq!( l.clone() * Nat::from(u32::MAX / 77), l.clone() * (u32::MAX/77));
}

#[test]
fn nat_mul_by_karatsuba() {
    let a = Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap();
    let b = Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap();
    let c = Nat::from_str("0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeff0000000000000000000000000000000000000000000000000000000000000001").unwrap();
    let z = Nat::with_capacity(32);
    Nat::mul_by_karatsuba(z.as_mut_vec(), a.as_slice(), b.as_slice());
    assert_eq!(z, c);
    
    let a = Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap();
    let b = Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap();
    let c = Nat::from_str("0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000001").unwrap();
    Nat::mul_by_karatsuba(z.as_mut_vec(), a.as_slice(), b.as_slice());
    assert_eq!(z, c);
    let a = Nat::from_str("0x123507af44107cfc63175d6cc354e6093bfeb7b0f5145641a0bc284bf1784696cc9791b18ab54de0114f6581d68041b66c7db").unwrap() ;
    let b = Nat::from_str("0xb9bd7d543685789d57cb918e833af352559021483cdb05cc21fd").unwrap();
    let c = Nat::from_str("0xd35cc9e369cf1fd0f297f4cf7ad21a1d9d65d9b421b51d5b689b0a47485a2c1582963dfc988179047a98dd36d5644070a0f8bb94fff1e6efeacc8ba03758fe7c8c574c12cfa377bedddabe6f").unwrap();
    Nat::mul_by_karatsuba(z.as_mut_vec(), a.as_slice(), b.as_slice());
    assert_eq!(z, c);
    let a = Nat::from_str("2938462938472983472983659726349017249287491026512746239764525612965293865296239471239874193284792387498274256129746192347").unwrap() ;
    let b = Nat::from_str("298472983472983471903246121093472394872319615612417471234712061").unwrap();
    let c = Nat::from_str("877051800070821244789099242710450134536982682006837233541161511456161001386576641869116186901815671895415144768179824202865342118174193449288433467901275304066981993483906649666797167").unwrap();
    Nat::mul_by_karatsuba(z.as_mut_vec(), a.as_slice(), b.as_slice());
    assert_eq!(z, c);
    let a = Nat::from(10u8);
    let b = a.deep_clone();
    let c = Nat::from(100u8);
    Nat::mul_by_karatsuba(z.as_mut_vec(), a.as_slice(), b.as_slice());
    assert_eq!(z, c);
    let b = Nat::from(0u32);
    let c = Nat::from(0u8);
    Nat::mul_by_karatsuba(z.as_mut_vec(), a.as_slice(), b.as_slice());
    assert_eq!(z, c);
    let b = Nat::from(1u32);
    let c = a.deep_clone();
    Nat::mul_by_karatsuba(z.as_mut_vec(), a.as_slice(), b.as_slice());
    assert_eq!(z, c);
    let a = Nat::from(0xffffffu64);
    let b = Nat::from(0xfffffffffu128);
    let c = Nat::from(0xfffffefff000001u128);
    Nat::mul_by_karatsuba(z.as_mut_vec(), a.as_slice(), b.as_slice());
    assert_eq!(z, c);
    let a = Nat::from_str("0xf9058301048250fabddeabf9320480284932084552541").unwrap();
     let b = Nat::from_str("0xf329053910428502fabcd9230494035242429890eacb").unwrap();
    let c = Nat::from_str("0xec882250900ba90c2088a4a5ee549ecc5152d7a50683a82daa24e03f6d6409468abf1ce1f01d9be845021f48b").unwrap();
    Nat::mul_by_karatsuba(z.as_mut_vec(), a.as_slice(), b.as_slice());
    assert_eq!(z, c);
    let a = Nat::from(u128::MAX);
    let b = Nat::from(u32::MAX);
    let c = Nat::from(u128::MAX);
    Nat::mul_by_karatsuba(z.as_mut_vec(), a.as_slice(), b.as_slice());
    assert_eq!(z, c * u32::MAX);
    let a = Nat::from(u128::MAX / 5);
    let b = Nat::from(u32::MAX);
    let c = a.deep_clone();
    Nat::mul_by_karatsuba(z.as_mut_vec(), a.as_slice(), b.as_slice());
    assert_eq!(z, c * u32::MAX);
    let a = Nat::from_str("0x123507af44107cfc63175d6cc354e6093bfeb7b0f5145641a0bc284bf1784696cc9791b18ab54de0114f6581d68041b66c7db").unwrap();
    let b = Nat::from(u32::MAX);
    let c = a.clone();
    Nat::mul_by_karatsuba(z.as_mut_vec(), a.as_slice(), b.as_slice());
    assert_eq!(z, c.clone() * u32::MAX);
    let b = Nat::from(u32::MAX / 77);
    Nat::mul_by_karatsuba(z.as_mut_vec(), a.as_slice(), b.as_slice());
    assert_eq!(z, c * (u32::MAX / 77));
}

#[test]
fn nat_div() {
    let l1 = Nat::from(100u8);
    let l2 = Nat::from(10u8);
    assert_eq!(l1.clone() / l2.clone(), Nat::from(10u8));
    assert_eq!(l1 / 10u32, Nat::from(10u8));
    assert_eq!(l2 / 100u32, Nat::from(0u8));
    let l1 = Nat::from_str("0xfffffffffff32908329058205820").unwrap();
    let l2 = Nat::from_str("0xff").unwrap();
    let quo = Nat::from_str("0x10101010100f41d2557e84060b8").unwrap();
    assert_eq!(l1.clone() / l2.clone(), quo);
    assert_eq!(l1.clone() / 0xffu32, quo);
    assert_eq!(l2 / l1, Nat::from(0u8));
    let l1 = Nat::from_str("0x39025820857032850384502853503850325fa3242de121").unwrap();
    let l2 = Nat::from_str("0x2048537058358afedead392582075275").unwrap();
    let quo = Nat::from_str("0x1c414f70ec1f027").unwrap();
    assert_eq!(l1.clone() / Nat::from(u32::MAX), l1.clone() / u32::MAX);
    assert_eq!(l1.clone() / Nat::from(u32::MAX / 101), l1.clone() / (u32::MAX / 101));
    assert_eq!(l1 / l2, quo);
    let l1 = Nat::from(0x1ad7f29abcau128);
    assert_eq!(l1.clone() / Nat::from(10u8), Nat::from(184467440737u128));
    assert_eq!(l1.clone() / 10, Nat::from(184467440737u128));
}

#[test]
fn nat_rem() {
    let l1 = Nat::from_str("0xffffffffffffff000000000000").unwrap();
    let l2 = Nat::from(255u32);
    assert_eq!(l1.clone() % l2, Nat::from(0u8));
    assert_eq!(l1 % 255u32, Nat::from(0u8));
    let l1 = Nat::from_str("0x39025820857032850384502853503850325fa3242de121").unwrap();
    let l2 = Nat::from_str("0x2048537058358afedead392582075275").unwrap();
    let rem = Nat::from_str("0xab9de6183b632a33dc2601ae78da14e").unwrap();
    assert_eq!(l1.clone() % Nat::from(u32::MAX), l1.clone() % u32::MAX);
    assert_eq!(l1.clone() % Nat::from(u32::MAX / 217), l1.clone() % (u32::MAX / 217));
    assert_eq!(l1 % l2, rem);
    let l1 = Nat::from_str("0xfffffffffff32908329058205820").unwrap();
    let l2 = Nat::from_str("0xff").unwrap();
    let quo = Nat::from_str("0xd8").unwrap();
    assert_eq!(l1.clone() % l2.clone(), quo);
    assert_eq!(l1.clone() % Nat::from(255u32), 0xd8u32);
    assert_eq!(l1.clone() % Nat::from(255u64), 0xd8u64);
    assert_eq!(l1.clone() % 255u32, 0xd8u32);
}

#[test]
fn nat_pow2() {
    let cases = [
        ("3290008573752325757353025730253207247022057235703", "108241564153638127123\
26338925222078355527665104927424021239791877758156389238060000928857697904209"),
        ("0x90000000fac90247577fffffffffffffff327075770257ffffffffff157025700000000000000000000000000003277faeb",
         "0x510000011a222291381d3647eaf2983fa600fe84244fe3d65c15277181259444346f541bc2ada3f9fc779dd57fbc3dde437a5dc\
5458d1feec4f59c6527798bef33f79f172a6e22d8fffa383f112f3237ba0000000000000000000009f3163f0869d3b9"
        ),
        ("0xfabcde1234567980abcdef0123456789fedcba0987654321009876654321\
0aefcdff9988776655443321009ffaaddeeeff90275205727535772673670673\
2afedcaf39205707520735737272737603672670367327630673670376036720\
67aedf",
         "0xf5956d127999586326220be8b7f4ec08e60e111b31c08e252a840fcb54f184b9997adcefd2\
c4f422acc103e6c6a05bed44345bdade4cbdc22bda89dd363a6c48fc42df2dfc0fd07301bd\
8d8ecb8f70617dcee2056e8b503fd323c7d2b402e38fd46c92b778b7cfe3bd0356a9188cb4\
8124aa0b0a7bafb31adeb694358bd1234eab7fed6e7b557a065d0963ed74ae6e0d44b183c3\
fb1bd6bdc94b5a2d86f4ba46bfdec80a7614b6d1614ca2027b5cc5209837a8beb6a374def3\
6df5360727eee5e641"
        ),
    ];
    
    cases.iter().for_each(|&x| {
        let a = Nat::from_str(x.0).unwrap();
        let b = Nat::from(2u32);
        let c = Nat::from_str(x.1).unwrap();
        assert_eq!(a.pow(b.clone()), c, "case: {}", x.0);
        assert_eq!(a.exp(&b, &Nat::from(0u32)), c, "case: {}", x.0);
    });
}

#[test]
fn nat_sqr() {
    let cases = [
        ("3290008573752325757353025730253207247022057235703", "108241564153638127123\
26338925222078355527665104927424021239791877758156389238060000928857697904209"),
        ("0x90000000fac90247577fffffffffffffff327075770257ffffffffff157025700000000000000000000000000003277faeb",
         "0x510000011a222291381d3647eaf2983fa600fe84244fe3d65c15277181259444346f541bc2ada3f9fc779dd57fbc3dde437a5dc\
5458d1feec4f59c6527798bef33f79f172a6e22d8fffa383f112f3237ba0000000000000000000009f3163f0869d3b9"
        ),
        ("0xfabcde1234567980abcdef0123456789fedcba0987654321009876654321\
0aefcdff9988776655443321009ffaaddeeeff90275205727535772673670673\
2afedcaf39205707520735737272737603672670367327630673670376036720\
67aedf",
         "0xf5956d127999586326220be8b7f4ec08e60e111b31c08e252a840fcb54f184b9997adcefd2\
c4f422acc103e6c6a05bed44345bdade4cbdc22bda89dd363a6c48fc42df2dfc0fd07301bd\
8d8ecb8f70617dcee2056e8b503fd323c7d2b402e38fd46c92b778b7cfe3bd0356a9188cb4\
8124aa0b0a7bafb31adeb694358bd1234eab7fed6e7b557a065d0963ed74ae6e0d44b183c3\
fb1bd6bdc94b5a2d86f4ba46bfdec80a7614b6d1614ca2027b5cc5209837a8beb6a374def3\
6df5360727eee5e641"
        ),
    ];
    
    cases.iter().for_each(|&x| {
        let a = Nat::from_str(x.0).unwrap();
        assert_eq!(a.sqr(), Nat::from_str(x.1).unwrap(), "case: {}", x.0);
    });
}

#[test]
fn nat_pow_mod() {
    // c.0 ^ c.1 mod c.2
    let cases = [
        ("0", "0", "0", "1"),
        ("0", "0", "1", "0"),
        ("1", "1", "1", "0"),
        ("2", "1", "1", "0"),
        ("2", "2", "1", "0"),
        ("10", "100000000000", "1", "0"),
        ("0x8000000000000000", "2", "0", "0x40000000000000000000000000000000"),
        ("0x8000000000000000", "2", "6719", "4944"),
        ("0x8000000000000000", "3", "6719", "5447"),
        ("0x8000000000000000", "1000", "6719", "1603"),
        ("0x8000000000000000", "1000000", "6719", "3199"),
        (
            "2938462938472983472983659726349017249287491026512746239764525612965293865296239471239874193284792387498274256129746192347",
            "298472983472983471903246121093472394872319615612417471234712061",
            "29834729834729834729347290846729561262544958723956495615629569234729836259263598127342374289365912465901365498236492183464",
            "23537740700184054162508175125554701713153216681790245129157191391322321508055833908509185839069455749219131480588829346291",
        ),
        (
            "11521922904531591643048817447554701904414021819823889996244743037378330903763518501116638828335352811871131385129455853417360623007349090150042001944696604737499160174391019030572483602867266711107136838523916077674888297896995042968746762200926853379",
            "426343618817810911523",
            "444747819283133684179",
            "42",
        ),
    ];
    
    let x = std::time::Instant::now();
    cases.iter().for_each(|&x| {
        let m = Nat::from_str(x.0).unwrap().pow_mod(Nat::from_str(x.1).unwrap(), Nat::from_str(x.2).unwrap());
        assert_eq!(m, Nat::from_str(x.3).unwrap(), "cases: ({}^{})%{}", x.0,x.1,x.2);
    });
    println!("{:?}", x.elapsed());
    
    let x = std::time::Instant::now();
    cases.iter().for_each(|&x| {
        let a = Nat::from_str(x.0).unwrap();
        let b = Nat::from_str(x.1).unwrap();
        let n = Nat::from_str(x.2).unwrap();
        let m = a.exp(&b, &n);
        assert_eq!(m, Nat::from_str(x.3).unwrap(), "cases: ({}^{})%{}", x.0,x.1,x.2);
    });
    println!("{:?}", x.elapsed());
}

#[test]
fn nat_random() {
    let nat = Nat::from_str("2938462938472983472983659726349017249287491026512746239764525612965293865296239471239874193284792387498274256129746192347").unwrap();
    println!("{:#b}",nat);
    let s = DefaultSeed::new().unwrap();
    let mut rng = CryptoRand::new(&s).unwrap();
    (0..10).for_each(|_| {
        println!("{:#b}", nat.random(&mut rng));
    })
}

#[test]
fn nat_prime_test() {
    let cases = [
        "2",
        "3",
        "5",
        "7",
        "11",
        "13756265695458089029",
        "13496181268022124907",
        "10953742525620032441",
        "17908251027575790097",
        
        // https://golang.org/issue/638
        "18699199384836356663",
        
        "98920366548084643601728869055592650835572950932266967461790948584315647051443",
        "94560208308847015747498523884063394671606671904944666360068158221458669711639",
        
        // https://primes.utm.edu/lists/small/small3.html
        "449417999055441493994709297093108513015373787049558499205492347871729927573118262811508386655998299074566974373711472560655026288668094291699357843464363003144674940345912431129144354948751003607115263071543163",
        "230975859993204150666423538988557839555560243929065415434980904258310530753006723857139742334640122533598517597674807096648905501653461687601339782814316124971547968912893214002992086353183070342498989426570593",
        "5521712099665906221540423207019333379125265462121169655563495403888449493493629943498064604536961775110765377745550377067893607246020694972959780839151452457728855382113555867743022746090187341871655890805971735385789993",
        "203956878356401977405765866929034577280193993314348263094772646453283062722701277632936616063144088173312372882677123879538709400158306567338328279154499698366071906766440037074217117805690872792848149112022286332144876183376326512083574821647933992961249917319836219304274280243803104015000563790123",
        
        // ECC primes: https://tools.ietf.org/html/draft-ladd-safecurves-02
        "3618502788666131106986593281521497120414687020801267626233049500247285301239",                                                                                  // Curve1174: 2^251-9
        "57896044618658097711785492504343953926634992332820282019728792003956564819949",                                                                                 // Curve25519: 2^255-19
        "9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576599",                                           // E-382: 2^382-105
        "42307582002575910332922579714097346549017899709713998034217522897561970639123926132812109468141778230245837569601494931472367",                                 // Curve41417: 2^414-17
        "6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151", // E-521: 2^521-1
    ];

    let composites = [
        "0",
        "1",
        "21284175091214687912771199898307297748211672914763848041968395774954376176754",
        "6084766654921918907427900243509372380954290099172559290432744450051395395951",
        "84594350493221918389213352992032324280367711247940675652888030554255915464401",
        "82793403787388584738507275144194252681",
        
        // Arnault, "Rabin-Miller Primality Test: Composite Numbers Which Pass It",
        // Mathematics of Computation, 64(209) (January 1995), pp. 335-361.
        // strong pseudoprime to prime bases 2 through 29
        "1195068768795265792518361315725116351898245581",
        // strong pseudoprime to all prime bases up to 200
        "8038374574536394912570796143419421081388376882875581458374889175222974273765333652186502336163960045457915042023603208766569966760987284043965408232928738791850869166857328267761771029389697739470167082304286871099974399765441448453411558724506334092790222752962294149842306881685404326457534018329786111298960644845216191652872597534901",
        
        // Extra-strong Lucas pseudoprimes. https://oeis.org/A217719
        "989",
        "3239",
        "5777",
        "10877",
        "27971",
        "29681",
        "30739",
        "31631",
        "39059",
        "72389",
        "73919",
        "75077",
        "100127",
        "113573",
        "125249",
        "137549",
        "137801",
        "153931",
        "155819",
        "161027",
        "162133",
        "189419",
        "218321",
        "231703",
        "249331",
        "370229",
        "429479",
        "430127",
        "459191",
        "473891",
        "480689",
        "600059",
        "621781",
        "632249",
        "635627",
        
        "3673744903",
        "3281593591",
        "2385076987",
        "2738053141",
        "2009621503",
        "1502682721",
        "255866131",
        "117987841",
        "587861",
        
        "6368689",
        "8725753",
        "80579735209",
        "105919633",
        
    ];

    let s = DefaultSeed::new().unwrap();
    let mut rng = CryptoRand::new(&s).unwrap();
    let s = 1usize;
    let his0 = Instant::now();
    cases.iter().for_each(|&x| {
        let nat = Nat::from_str(x).unwrap();
        let his = Instant::now();
        assert!(nat.probably_prime_test(s, &mut rng), "case: {} is prime", x);
        println!("time: {:?}, case=>{}, len:{}", his.elapsed(), x, nat.bits_len());
    });
    composites.iter().for_each(|&x| {
        let nat = Nat::from_str(x).unwrap();
        let his = Instant::now();
        assert!(!nat.probably_prime_test(s, &mut rng), "case: {} is composites", x);
        println!("time: {:?}, case=>{}, len:{}", his.elapsed(), x, nat.bits_len());
    });
    println!("total time: {:?}", Instant::now().duration_since(his0));
}


#[test]
fn nat_sqrt() {
    let cases = [
        ("12206284081173349864898827262724183837227000064385444", "110482053208534054039584038"),
        ("12206284081173349864898827483688290254295108143553520", "110482053208534054039584038"),
        ("12206284081173349864898827483688290254295108143553521", "110482053208534054039584039"),
        ("153703855624064693364322134828544142297057513119669708159894633648930223634687381897262578548070240793432433518308472746550767582677051942338528984321", "392050832959279265659236536583628569256915965495693645293925629365386592639"),
    ];
    
    cases.iter().for_each(|&e| {
        let a = Nat::from_str(e.0).unwrap();
        let b = Nat::from_str(e.1).unwrap();
        let s = a.sqrt();
        assert_eq!(s, b, "case: {}", e.0);
    });
}