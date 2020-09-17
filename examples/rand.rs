extern crate rmath;

use rmath::rand::{DefaultSeed, DefaultRand, Seed, CryptoRand};

fn main() {
    let s = DefaultSeed::<u32>::new().unwrap();
    let s64 = DefaultSeed::<u64>::new().unwrap();
    println!("{:#x}", s.seed().unwrap());
    println!("{:#x}", s64.seed().unwrap());
    let mut rander = DefaultRand::new(&s).unwrap();
    let mut rander_64 = DefaultRand::new(&s64).unwrap();

    let mut lcr0 = rmath::minstd_rand0!(s).unwrap();
    let mut lcr = rmath::minstd_rand!(s).unwrap();
    let mut mtr= rmath::mt19937!(s).unwrap();
    let mut mtr_64 = rmath::mt19937_64!(s64).unwrap();
    let mut lfr = rmath::ranlux24_base!(s).unwrap();
    let mut lfr_64 = rmath::ranlux48_base!(s64).unwrap();
    let mut crypto_rand = CryptoRand::new(&s).unwrap();
    let mut crypto_rand_64 = CryptoRand::new(&s64).unwrap();
    println!("======================================================");
    let dr_itr = rander.iter_mut();
    dr_itr.take(10).for_each(|x| {
        println!("{:#x}", x);
    });
    println!("======================================================");
    let dr_itr = rander_64.iter_mut();
    dr_itr.take(10).for_each(|x| {
        println!("{:#x}", x);
    });
    println!("======================================================");
    let dr_itr = lcr0.iter_mut();
    dr_itr.take(10).for_each(|x| {
        println!("{:#x}", x);
    });
    println!("======================================================");
    let dr_itr = lcr.iter_mut();
    dr_itr.take(10).for_each(|x| {
        println!("{:#x}", x);
    });
    println!("======================================================");
    let dr_itr = mtr.iter_mut();
    dr_itr.take(10).for_each(|x| {
        println!("{:#x}", x);
    });
    println!("======================================================");
    let dr_itr = mtr_64.iter_mut();
    dr_itr.take(10).for_each(|x| {
        println!("{:#x}", x);
    });
    println!("======================================================");
    let dr_itr = lfr_64.iter_mut();
    dr_itr.take(10).for_each(|x| {
        println!("{:#x}", x);
    });
    println!("======================================================");
    let dr_itr = lfr.iter_mut();
    dr_itr.take(10).for_each(|x| {
        println!("{:#x}", x);
    });
    println!("======================================================");
    let dr_itr = crypto_rand.iter_mut();
    dr_itr.take(10).for_each(|x| {
        println!("{:#x}", x);
    });
    println!("======================================================");
    let dr_itr = crypto_rand_64.iter_mut();
    dr_itr.take(10).for_each(|x| {
        println!("{:#x}", x);
    });
}
