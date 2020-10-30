use crate::bigint::{Rat, BigInt};
use std::str::FromStr;

#[test]
fn rat_zero() {
    let (x, y) = (Rat::from_frac(0, 42).unwrap(), Rat::from_str("0/1").unwrap());
    
    assert_eq!(x, y);
    
    let z = x.clone() + y.clone();
    assert_eq!(z, x);
    
    let z = x.clone() - y.clone();
    assert_eq!(z, x);
    
    let z = x.clone() * y.clone();
    assert_eq!(z, x);
    
    let z = x.clone() / Rat::from(1.0);
    assert_eq!(z, x);
}

const VALID_STR: [(&str, &str); 23] = [
    ("0", "0"),
    ("-0", "0"),
    ("1", "1"),
    ("-1", "-1"),
    ("1.", "1"),
    ("1.e0", "1"),
    ("1.e1", "10"),
    ("-0.1", "-1/10"),
    ("-.1", "-1/10"),
    ("2/4", "1/2"),
    (".25", "1/4"),
    ("-1/5", "-1/5"),
    ("8129567.7690E14", "812956776900000000000"),
    ("78189.e+4", "781890000"),
    ("553019.8935e+8", "55301989350000"),
    ("98765432109876543210987654321.e-10", "98765432109876543210987654321/10000000000"),
    ("9877861857500000.E-7", "3951144743/4"),
    ("2169378.417e-3", "2169378417/1000000"),
    ("884243222337379604041632732738665534", "884243222337379604041632732738665534"),
    ("53/70893980658822810696", "53/70893980658822810696"),
    ("106/141787961317645621392", "53/70893980658822810696"),
    ("204211327800791583.81095", "4084226556015831676219/20000"),
    ("0.e9999999999", "0"), // issue #16176
];


#[test]
fn rat_sign() {
    VALID_STR.iter().for_each(|&e| {
        let s = Rat::from_str(e.0).unwrap();
        let zero = Rat::from(0u32);
        let x = s.signnum().unwrap();
        if x == 0 {
            assert_eq!(s, zero, "case: {}", e.0);
        } else if x > 0 {
            assert!(s > zero, "case: {}", e.0);
        } else {
            assert!(s < zero, "case: {}", e.0);
        }
    });
}

#[test]
fn rat_partial_cmp() {
    let cases = [
        ("0", "0/1", 0),
        ("1/1", "1", 0),
        ("-1", "-2/2", 0),
        ("1", "0", 1),
        ("0/1", "1/1", -1),
        ("-5/1434770811533343057144", "-5/1434770811533343057145", -1),
        ("49832350382626108453/8964749413", "49832350382626108454/8964749413", -1),
        ("-37414950961700930/7204075375675961", "37414950961700930/7204075375675961", -1),
        ("37414950961700930/7204075375675961", "74829901923401860/14408150751351922", 0),
    ];
    
    cases.iter().for_each(|&e| {
        let a = Rat::from_str(e.0).unwrap();
        let b = Rat::from_str(e.1).unwrap();
        let c = e.2;
        if c == 0 {
            assert_eq!(a, b, "case: {}.partial_cmp({})", e.0, e.1);
        } else if c > 0 {
            assert!(a > b, "case: {}.partial_cmp({})", e.0, e.1);
        } else {
            assert!(a < b, "case: {}.partial_cmp({})", e.0, e.1);
        }
    });
}

#[test]
fn rat_is_integer() {
    let one = BigInt::from(1u32);
    VALID_STR.iter().for_each(|&e| {
        let a = Rat::from_str(e.0).unwrap();
        let left = a.is_integer().unwrap();
        let right = a.denominator() == &one;
        assert_eq!(left, right, "case: {}", e.0);
    });
}


#[test]
fn rat_abs() {
    let zero = Rat::from(0u32);
    VALID_STR.iter().for_each(|&e| {
        let a = Rat::from_str(e.0).unwrap();
        let b = if a < zero {
            zero.clone() - a.clone()
        } else {
            a.clone()
        };
        
        assert_eq!(b, a.abs(), "case: {}", e.0);
    });
}

#[test]
fn rat_neg() {
    let zero = Rat::from(0u32);
    VALID_STR.iter().for_each(|&e| {
        let a = Rat::from_str(e.0).unwrap();
        let b = zero.clone() - a.clone();
        assert_eq!(b, -a, "case: {}", e.0);
    });
}

#[test]
fn rat_inv() {
    let zero = Rat::from(0u32);
    VALID_STR.iter().for_each(|&e| {
        let a = Rat::from_str(e.0).unwrap();
        if a != zero {
            let inv = Rat::from_frac_bigint(a.denominator(), a.numerator()).unwrap();
            assert_eq!(inv, a.inv().unwrap(), "case: {}", e.0);
        }
    });
}

#[test]
fn rat_arith() {
    let cases = [
        ("0", "0", "0", "0"),
        ("0", "1", "1", "0"),
        ("-1", "0", "-1", "0"),
        ("-1", "1", "0", "-1"),
        ("1", "1", "2", "1"),
        ("1/2", "1/2", "1", "1/4"),
        ("1/4", "1/3", "7/12", "1/12"),
        ("2/5", "-14/3", "-64/15", "-28/15"),
        ("4707/49292519774798173060", "-3367/70976135186689855734", "84058377121001851123459/1749296273614329067191168098769082663020", "-1760941/388732505247628681598037355282018369560"),
        ("-61204110018146728334/3", "-31052192278051565633/2", "-215564796870448153567/6", "950260896245257153059642991192710872711/3"),
        ("-854857841473707320655/4237645934602118692642972629634714039", "-18/31750379913563777419", "-27/133467566250814981", "15387441146526731771790/134546868362786310073779084329032722548987800600710485341"),
        ("618575745270541348005638912139/19198433543745179392300736", "-19948846211000086/637313996471", "27674141753240653/30123979153216", "-6169936206128396568797607742807090270137721977/6117715203873571641674006593837351328"),
        ("-3/26206484091896184128", "5/2848423294177090248", "15310893822118706237/9330894968229805033368778458685147968", "-5/24882386581946146755650075889827061248"),
        ("26946729/330400702820", "41563965/225583428284", "1238218672302860271/4658307703098666660055", "224002580204097/14906584649915733312176"),
        ("-8259900599013409474/7", "-84829337473700364773/56707961321161574960", "-468402123685491748914621885145127724451/396955729248131024720", "350340947706464153265156004876107029701/198477864624065512360"),
        ("575775209696864/1320203974639986246357", "29/712593081308", "410331716733912717985762465/940768218243776489278275419794956", "808/45524274987585732633"),
        ("1786597389946320496771/2066653520653241", "6269770/1992362624741777", "3559549865190272133656109052308126637/4117523232840525481453983149257", "8967230/3296219033"),
        ("-36459180403360509753/32150500941194292113930", "9381566963714/9633539", "301622077145533298008420642898530153/309723104686531919656937098270", "-3784609207827/3426986245"),
    ];
    
    let zero = Rat::from(0u32);
    cases.iter().for_each(|&e| {
        let (x, y, sum, prod) = (
            Rat::from_str(e.0).unwrap(), Rat::from_str(e.1).unwrap(), Rat::from_str(e.2).unwrap(), Rat::from_str(e.3).unwrap(),
            );
        
        assert_eq!(x.clone() + y.clone(), sum.clone(), "case:{} + {}", e.0, e.1);
        assert_eq!(sum.clone() - y.clone(), x.clone(), "case: {} - {}", e.2, e.1);
        assert_eq!(x.clone() * y.clone(), prod.clone(), "case: {} * {}", e.0, e.1);
        
        if y != zero {
            let q = prod.clone() / y.clone();
            assert_eq!(x.clone(), q.clone(), "case: {} / {}", e.3, e.1);
        }
        
        if x != zero {
            let q = prod.clone() / x.clone();
            assert_eq!(y.clone(), q.clone(), "case: {} / {}", e.3, e.0);
        }
    });
}

#[test]
fn rat_frac() {
    let (x, y, q) = (Rat::from_frac(3,1).unwrap(), Rat::from_frac(2,1).unwrap(),
                     Rat::from_frac(3,2).unwrap());
    assert_eq!(q.clone(), x.clone() / y.clone(), "case: {} / {}", x.clone(), y.clone());
    assert_eq!(q.inv().unwrap(), y.clone() / x.clone(), "case: {} / {}", y.clone(), x.clone());

    let q = Rat::from_frac(2,3).unwrap();
    assert_eq!(q.clone(), y.clone() / x.clone(), "case: {} / {}", y.clone(), x.clone());

    let q = Rat::from_frac(3,3).unwrap();
    assert_eq!(q.clone(), x.clone()/ x.clone(), "case: {} / {}", x.clone(), x.clone());
    
    let case = [
        (0, 1, "0"),
        (0, -1, "0"),
        (1, 1, "1"),
        (-1, 1, "-1"),
        (1, -1, "-1"),
        (-1, -1, "1"),
    ];
    
    case.iter().for_each(|&e| {
        let (x, y) = (Rat::from_frac(e.0, e.1).unwrap(), Rat::from_str(e.2).unwrap());
        assert_eq!(x, y, "case: {}/{}", e.0, e.1);
    });
    
    let case = [
        ("-9223372036854775808", "-9223372036854775808", "1"),
        ];
    case.iter().for_each(|&e| {
        let (x, y) = (Rat::from_frac_bigint(&BigInt::from_str(e.0).unwrap(), &BigInt::from_str(e.1).unwrap()).unwrap(), 
                      Rat::from_str(e.2).unwrap());
        assert_eq!(x, y, "case: {}/{}", e.0, e.1);
    });
}