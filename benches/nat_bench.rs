#![feature(test)]

extern crate test;

use test::Bencher;
use rmath::bigint::Nat;
use std::str::FromStr;
use rmath::rand::{CryptoRand, DefaultSeed};

#[bench]
fn nat_mul(b: &mut Bencher) {
    b.iter(|| {
        let _ = Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap() *
                       Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap();
        let _ = Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap() *
                       Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap();
        let _ = Nat::from_str("0x123507af44107cfc63175d6cc354e6093bfeb7b0f5145641a0bc284bf1784696cc9791b18ab54de0114f6581d68041b66c7db").unwrap() *
                       Nat::from_str("0xb9bd7d543685789d57cb918e833af352559021483cdb05cc21fd").unwrap();
        let _ = Nat::from_str("2938462938472983472983659726349017249287491026512746239764525612965293865296239471239874193284792387498274256129746192347").unwrap() *
                       Nat::from_str("298472983472983471903246121093472394872319615612417471234712061").unwrap();
        let _ = Nat::from_str("0xf9058301048250fabddeabf9320480284932084552541").unwrap() * Nat::from_str("0xf329053910428502fabcd9230494035242429890eacb").unwrap();
        let m = Nat::from_str("11521922904531591643048817447554701904414021819823889996244743037378330903763518501116638828335352811871131385129455853417360623007349090150042001944696604737499160174391019030572483602867266711107136838523916077674888297896995042968746762200926853379").unwrap();
        let mm = Nat::from_str("132754707417969709071520913953150018674028397187840392482040376246690586667563465313754728983140614311023330588338584519494816082808802757576723626979148131665716420054994459252371545991867826226044967226902943970336055338722678643684695617436438527026987305947020775148894065847620914397220804830164550914287609717627447949778761358443479465789746235738152749867139029328299380633642942992192185932412578698966382535294856314633011368627178673993077019158590397083090972027015095881618004786163717641").unwrap();
        let _ = m * mm;
    });
}

#[bench]
fn nat_mul_by_karatsuba(b: &mut Bencher) {
    b.iter(|| {
        let a = Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap();
        let b = Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap();
        let _ = a.mul_karatsuba(&b);
        let a = Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap();
        let b = Nat::from_str("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap();
        let _ = a.mul_karatsuba(&b);
        let a = Nat::from_str("0x123507af44107cfc63175d6cc354e6093bfeb7b0f5145641a0bc284bf1784696cc9791b18ab54de0114f6581d68041b66c7db").unwrap();
        let b = Nat::from_str("0xb9bd7d543685789d57cb918e833af352559021483cdb05cc21fd").unwrap();
        let _ = a.mul_karatsuba(&b);
        let a = Nat::from_str("2938462938472983472983659726349017249287491026512746239764525612965293865296239471239874193284792387498274256129746192347").unwrap();
        let b = Nat::from_str("298472983472983471903246121093472394872319615612417471234712061").unwrap();
        let _ = a.mul_karatsuba(&b);
        let a = Nat::from_str("0xf9058301048250fabddeabf9320480284932084552541").unwrap();
        let b = Nat::from_str("0xf329053910428502fabcd9230494035242429890eacb").unwrap();
        let _ = a.mul_karatsuba(&b);
        let a = Nat::from_str("11521922904531591643048817447554701904414021819823889996244743037378330903763518501116638828335352811871131385129455853417360623007349090150042001944696604737499160174391019030572483602867266711107136838523916077674888297896995042968746762200926853379").unwrap();
        let b = Nat::from_str("132754707417969709071520913953150018674028397187840392482040376246690586667563465313754728983140614311023330588338584519494816082808802757576723626979148131665716420054994459252371545991867826226044967226902943970336055338722678643684695617436438527026987305947020775148894065847620914397220804830164550914287609717627447949778761358443479465789746235738152749867139029328299380633642942992192185932412578698966382535294856314633011368627178673993077019158590397083090972027015095881618004786163717641").unwrap();
        let _ = a.mul_karatsuba(&b);
    });
}

#[bench]
fn nat_sqr_by_pow(b: &mut Bencher) {
    b.iter(|| {
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
            let _ = Nat::from_str(x.0).unwrap().pow(Nat::from(2u32));
        });
    });
}

#[bench]
fn nat_sqr(b: &mut Bencher) {
    b.iter(|| {
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
            let _ = Nat::from_str(x.0).unwrap().sqr();
        });
    });
}

#[bench]
fn nat_div(b: &mut Bencher) {
    let cases = [
        ("100", "10"),
        ("0xfffffffffff32908329058205820", "0xff"),
        ("0xff", "0xfffffffffff32908329058205820"),
        ("0x39025820857032850384502853503850325fa3242de121", "0x2048537058358afedead392582075275"),
        ("0x1ad7f29abca", "10")
    ];
    b.iter(|| {
        cases.iter().for_each(|&x| {
            let _ = Nat::from_str(x.0).unwrap() / Nat::from_str(x.1).unwrap();
        });
    });
}

#[bench]
fn nat_rem(b: &mut Bencher) {
    let cases = [
        ("0xffffffffffffff000000000000", "255"),
        ("0x39025820857032850384502853503850325fa3242de121", "0xab9de6183b632a33dc2601ae78da14e"),
        ("0xfffffffffff32908329058205820", "0xff")
    ];
    b.iter(|| {
        cases.iter().for_each(|&x| {
            let _ = Nat::from_str(x.0).unwrap() % Nat::from_str(x.1).unwrap();
        });
    });
}

#[bench]
fn nat_pow_mod(b: &mut Bencher) {
    b.iter(|| {
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

        cases.iter().for_each(|&x| {
            let _m = Nat::from_str(x.0).unwrap().pow_mod(Nat::from_str(x.1).unwrap(), Nat::from_str(x.2).unwrap());
        });
    });
}


#[bench]
fn nat_pow_mod_by_exp(b: &mut Bencher) {
    b.iter(|| {
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

        cases.iter().for_each(|&x| {
            let a = Nat::from_str(x.0).unwrap();
            let b  = Nat::from_str(x.1).unwrap();
            let c = Nat::from_str(x.2).unwrap();
            let _m = a.exp(&b, &c);
        });
    });
}

#[bench]
fn nat_random(b: &mut Bencher) {
    let nat = Nat::from_str("2938462938472983472983659726349017249287491026512746239764525612965293865296239471239874193284792387498274256129746192347").unwrap();
    let s = DefaultSeed::new().unwrap();
    let mut rng = CryptoRand::new(&s).unwrap();
    b.iter(|| {
        let _r = nat.random(&mut rng);
    });
}

#[bench]
fn nat_shl(b: &mut Bencher) {
    b.iter(|| {
        let nat = Nat::from_str("11521922904531591643048817447554701904414021819823889996244743037378330903763518501116638828335352811871131385129455853417360623007349090150042001944696604737499160174391019030572483602867266711107136838523916077674888297896995042968746762200926853379").unwrap();
        let _n = nat.clone() << 333usize;
        let _n = nat >> 37;
    });
}
