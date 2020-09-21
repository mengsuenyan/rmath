use rmath::bigint::{Nat, BigInt};
use std::str::FromStr;

fn main() {
    let a = Nat::from(u128::MAX);
    let b = Nat::from(u128::MAX);
    let _sum = a + b;

    let a = Nat::from(u128::MAX);
    let b = Nat::from(u128::MAX);
    // the `ops::{Add, Sub, ...}` will own the ownership of its parameters.
    // you can clone the parameter to receive the shared ownership when you want to use it later.
    let sum = a.clone() + b.clone();
    let diff = a.clone() - b.clone();
    println!("{:#x} + {:#x} = {:#x}", a, b, sum);
    println!("{:#x} - {:#x} = {:#x}", a, b, diff);

    let a = Nat::from_str("2938462938472983472983659726349017249287491026512746239764525612965293865296239471239874193284792387498274256129746192347").unwrap();
    let b = Nat::from_str("298472983472983471903246121093472394872319615612417471234712061").unwrap();
    println!("{} * {} = {}", a.clone(), b.clone(), a*b );
    
    let (a, b) = (Nat::from(u32::MAX), Nat::from(u32::MAX));
    let sum = a.clone() + b.clone();
    let mul = sum * a.clone() + b.clone();
    println!("(({}+{})*{}) + {} = {}", a, b, a, b, mul);

    let (a, b) = (BigInt::from(u32::MAX), BigInt::from(u32::MAX));
    let sum = a.clone() + b.clone();
    let mul = sum * a.clone() + b.clone();
    println!("(({}+{})*{}) + {} = {}", a, b, a, b, mul);


    let a = BigInt::from_str("2938462938472983472983659726349017249287491026512746239764525612965293865296239471239874193284792387498274256129746192347").unwrap();
    let b = BigInt::from_str("298472983472983471903246121093472394872319615612417471234712061").unwrap();
    println!("{} * {} = {}", a.clone(), b.clone(), a*b );
}