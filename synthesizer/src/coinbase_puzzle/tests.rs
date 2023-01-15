// Copyright (C) 2019-2022 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use super::*;
use aleo_std::{end_timer, start_timer};
use console::{account::*, network::Testnet3, prelude::cfg_into_iter};
use snarkvm_curves::bls12_377::Fr;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::BigInteger;
use snarkvm_utilities::BigInteger256;
use snarkvm_utilities::ToBytes;
use snarkvm_utilities::Uniform;

use rand::RngCore;

use std::ops::Add;
use std::time::{Duration, Instant};

use blake2::Digest;

use num_bigint::BigUint;

const ITERATIONS: u64 = 100;

#[test]
fn test_coinbase_puzzle() {
    let mut rng = TestRng::default();

    let max_degree = 1 << 15;
    let max_config = PuzzleConfig { degree: max_degree };
    let srs = CoinbasePuzzle::<Testnet3>::setup(max_config).unwrap();

    for log_degree in 5..10 {
        let degree = (1 << log_degree) - 1;
        let config = PuzzleConfig { degree };
        let puzzle = CoinbasePuzzle::<Testnet3>::trim(&srs, config).unwrap();
        let epoch_challenge = EpochChallenge::new(rng.next_u32(), Default::default(), degree).unwrap();

        for batch_size in 1..10 {
            let solutions = (0..batch_size)
                .map(|_| {
                    let private_key = PrivateKey::<Testnet3>::new(&mut rng).unwrap();
                    let address = Address::try_from(private_key).unwrap();
                    let nonce = u64::rand(&mut rng);
                    puzzle.prove(&epoch_challenge, address, nonce, None).unwrap()
                })
                .collect::<Vec<_>>();
            let full_solution = puzzle.accumulate_unchecked(&epoch_challenge, &solutions).unwrap();
            assert!(puzzle.verify(&full_solution, &epoch_challenge, 0u64, 0u64).unwrap());

            let bad_epoch_challenge = EpochChallenge::new(rng.next_u32(), Default::default(), degree).unwrap();
            assert!(!puzzle.verify(&full_solution, &bad_epoch_challenge, 0u64, 0u64).unwrap());
        }
    }
}

#[test]
fn test_prover_solution_minimum_target() {
    let mut rng = TestRng::default();

    let max_degree = 1 << 15;
    let max_config = PuzzleConfig { degree: max_degree };
    let srs = CoinbasePuzzle::<Testnet3>::setup(max_config).unwrap();

    for log_degree in 5..10 {
        let degree = (1 << log_degree) - 1;
        let config = PuzzleConfig { degree };
        let puzzle = CoinbasePuzzle::<Testnet3>::trim(&srs, config).unwrap();
        let epoch_challenge = EpochChallenge::new(rng.next_u32(), Default::default(), degree).unwrap();

        for _ in 0..ITERATIONS {
            let private_key = PrivateKey::<Testnet3>::new(&mut rng).unwrap();
            let address = Address::try_from(private_key).unwrap();
            let nonce = u64::rand(&mut rng);

            let solution = puzzle.prove(&epoch_challenge, address, nonce, None).unwrap();
            let proof_target = solution.to_target().unwrap();

            // Assert that the operation will pass if the minimum target is low enough.
            assert!(puzzle.prove(&epoch_challenge, address, nonce, Some(proof_target.saturating_sub(1))).is_ok());

            // Assert that the operation will fail if the minimum target is too high.
            assert!(puzzle.prove(&epoch_challenge, address, nonce, Some(proof_target.saturating_add(1))).is_err());
        }
    }
}

#[test]
fn test_edge_case_for_degree() {
    let mut rng = rand::thread_rng();

    // Generate srs.
    let max_degree = 1 << 15;
    let max_config = PuzzleConfig { degree: max_degree };
    let srs = CoinbasePuzzle::<Testnet3>::setup(max_config).unwrap();

    // Generate PK and VK.
    let degree = (1 << 13) - 1; // IF YOU ADD `- 1` THIS WILL PASS
    let puzzle = CoinbasePuzzle::<Testnet3>::trim(&srs, PuzzleConfig { degree }).unwrap();

    // Generate proof inputs
    let private_key = PrivateKey::<Testnet3>::new(&mut rng).unwrap();
    let address = Address::try_from(private_key).unwrap();
    let epoch_challenge = EpochChallenge::new(rng.gen(), Default::default(), degree).unwrap();

    // Generate a prover solution.
    let prover_solution = puzzle.prove(&epoch_challenge, address, rng.gen(), None).unwrap();
    let coinbase_solution = puzzle.accumulate_unchecked(&epoch_challenge, &[prover_solution]).unwrap();
    assert!(puzzle.verify(&coinbase_solution, &epoch_challenge, 0u64, 0u64).unwrap());
}
// KZG10::commit_lagrange
//
//
//
#[test]
fn test_cuda_parallel() {
    let start = Instant::now();

    println!("test cuda parallel");

    let duration = start.elapsed();
    println!("Time elapsed in expensive_function() is: {:?}", duration);
    assert!(1 == 1);
}

#[test]
fn test_polynomial() {
    println!("test_polynomial()");
    // let mut rng = TestRng::default();

    let max_degree = 1 << 15;
    let max_config = PuzzleConfig { degree: max_degree };
    let srs = CoinbasePuzzle::<Testnet3>::setup(max_config).unwrap();

    let log_degree = 2;
    let degree = (1 << log_degree) - 1;
    let config = PuzzleConfig { degree };
    let puzzle = CoinbasePuzzle::<Testnet3>::trim(&srs, config).unwrap();
    let epoch_number = 0x11ABAEAA;
    // let epoch_block_hash = "ab1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq5g436j";
    // let epoch_challenge = EpochChallenge::new(epoch_number, Default::default(), degree).unwrap();
    // default value is data , F::zero()

    println!("Begin EpochChallenge::new()");
    let epoch_challenge = EpochChallenge::new(epoch_number, Default::default(), degree).unwrap();
    // 这里会生成一个product_domain, 使用到的算法，和后续是一样的!

    println!("epoch_number: {:#X}", epoch_challenge.epoch_number());
    println!("epoch_block_hash: {}", epoch_challenge.epoch_block_hash());
    println!("epoch_polynomial: {:?}", epoch_challenge.epoch_polynomial());
    println!("epoch_polynomail_evaluations: {:?}", epoch_challenge.epoch_polynomial_evaluations());

    // let private_key = PrivateKey::<Testnet3>::new(&mut rng).unwrap();
    let private_key =
        PrivateKey::<Testnet3>::from_str("APrivateKey1zkp686TthAY2rhCzhLwDZEeYkxA33vNwC2yB8va7FDP6yEM").unwrap();
    //let private_key = "APrivateKey1zkp686TthAY2rhCzhLwDZEeYkxA33vNwC2yB8va7FDP6yEM";
    println!("private_key: {}", private_key);
    let address = Address::try_from(private_key).unwrap();
    println!("address: {}", address);
    //let nonce = u64::rand(&mut rng);
    let nonce: u64 = 0x11110000;
    println!("nonce: {:#X}", nonce);

    // let polynomial = puzzle.prover_polynomial(epoch_challenge, address, nonce).unwrap();
    let polynomial = puzzle.prove_tst(&epoch_challenge, address, nonce, None).unwrap();
    // let proof_target = solution.to_target().unwrap();
    // let polynomial = puzzle.my_prover_polynomial(epoch_challenge, address, nonce);
    println!("polynomial-> : {:?}", polynomial);
    println!("polynomial degree: {}", polynomial.degree());
    for element in polynomial.coeffs.iter() {
        println!("{}, ", element);
    }

    let pk = puzzle.coinbase_proving_key().unwrap();

    println!("pk.fft_precomputation: {:?}", pk.fft_precomputation);

    let polynomial_evaluations = pk.product_domain.in_order_fft_with_pc(&polynomial, &pk.fft_precomputation);
    println!("polynomial_evaluations: {:?}", polynomial_evaluations);

    println!("epoch challenge.evaluations: {:?}", epoch_challenge.epoch_polynomial_evaluations().evaluations);

    let product_evaluations = pk.product_domain.mul_polynomials_in_evaluation_domain(
        &polynomial_evaluations,
        &epoch_challenge.epoch_polynomial_evaluations().evaluations,
    );

    println!("product_evaluations: {:?}", product_evaluations);

    assert!(1 == 1);
}

#[test]
fn test_blake2b512() {
    println!("test_blake2b512()");
    let max_degree = 1 << 15;
    let max_config = PuzzleConfig { degree: max_degree };
    let srs = CoinbasePuzzle::<Testnet3>::setup(max_config).unwrap();

    let log_degree = 2;
    let degree = (1 << log_degree) - 1;
    let config = PuzzleConfig { degree };
    let puzzle = CoinbasePuzzle::<Testnet3>::trim(&srs, config).unwrap();
    let epoch_number = 0x11ABAEAA;

    let epoch_challenge = EpochChallenge::<Testnet3>::new(epoch_number, Default::default(), degree).unwrap();

    println!("epoch_number: {:#X}", epoch_challenge.epoch_number());
    println!("epoch_block_hash: {}", epoch_challenge.epoch_block_hash());
    println!("epoch_polynomial: {:?}", epoch_challenge.epoch_polynomial());
    println!("epoch_polynomail_evaluations: {:?}", epoch_challenge.epoch_polynomial_evaluations());

    let private_key =
        PrivateKey::<Testnet3>::from_str("APrivateKey1zkp686TthAY2rhCzhLwDZEeYkxA33vNwC2yB8va7FDP6yEM").unwrap();
    //let private_key = "APrivateKey1zkp686TthAY2rhCzhLwDZEeYkxA33vNwC2yB8va7FDP6yEM";
    println!("private_key: {}", private_key);
    let address = Address::try_from(private_key).unwrap();
    println!("address: {}", address);
    //let nonce = u64::rand(&mut rng);
    let nonce: u64 = 0x11110000;
    println!("nonce: {:#X}", nonce);

    let mut bytes = [0u8; 76];
    bytes[..4].copy_from_slice(&epoch_challenge.epoch_number().to_bytes_le().unwrap());
    bytes[4..36].copy_from_slice(&epoch_challenge.epoch_block_hash().to_bytes_le().unwrap());
    bytes[36..68].copy_from_slice(&address.to_bytes_le().unwrap());
    bytes[68..].copy_from_slice(&nonce.to_le_bytes());

    // Hash the input.
    let hash = blake2::Blake2s256::digest(bytes);

    println!("1st hash: {:?}", hash);
    for i in 0..hash.len() {
        print!("{:#X} ", hash[i]);
    }
    println!("\n1st hash in Hex\n");
    // <<N::PairingCurve as PairingEngine>::Fr>

    // let iters: Vec<_> = cfg_into_iter!(0..16)
    //     .map(|counter| {
    //         println!("counter: {}", counter);
    //         counter
    //     }).collect();
    // println!("iters: {:?}", iters);

    for c in 0..16 {
        let cter: u32 = c;
        println!("== {} ==", cter);
        let mut input_with_counter = [0u8; 36];
        input_with_counter[..32].copy_from_slice(&hash);
        println!("cter to_le_bytes: {:?}", cter.to_le_bytes());
        input_with_counter[32..].copy_from_slice(&cter.to_le_bytes());

        println!("input with counter len(): {}", input_with_counter.len());

        println!("input to blake2b512");
        for i in 0..input_with_counter.len() {
            print!("{:#X} ", input_with_counter[i]);
        }

        let hash2 = blake2::Blake2b512::digest(input_with_counter);
        println!("\nhash2 out:");
        println!("{:?}", hash2);

        for i in 0..hash2.len() {
            print!("{:#X} ", hash2[i]);
        }
        println!("\n-----");
    }

    assert_eq!(1, 1);
}
#[test]
fn test_from_bytes_le() {
    let input0: [u8; 64] = [
        139, 29, 95, 238, 203, 131, 205, 41, 144, 20, 224, 248, 155, 28, 242, 107, 11, 105, 217, 94, 4, 98, 19, 236,
        253, 104, 85, 49, 13, 26, 225, 252, 253, 123, 174, 25, 145, 165, 178, 187, 228, 35, 59, 182, 54, 166, 157, 152,
        46, 247, 3, 224, 72, 183, 251, 215, 241, 221, 153, 177, 207, 200, 102, 161,
    ];
    let input1: [u8; 64] = [
        16, 32, 127, 204, 149, 67, 173, 241, 73, 2, 190, 206, 45, 179, 201, 3, 248, 219, 6, 4, 125, 129, 47, 228, 110,
        108, 105, 168, 138, 73, 20, 15, 54, 138, 227, 153, 114, 78, 173, 110, 147, 186, 46, 2, 166, 2, 74, 157, 13,
        247, 99, 135, 192, 178, 189, 40, 150, 9, 170, 38, 13, 1, 6, 153,
    ];
    let input2: [u8; 64] = [
        160, 172, 81, 36, 52, 124, 94, 207, 231, 202, 2, 156, 3, 88, 75, 149, 245, 158, 177, 250, 24, 231, 160, 201,
        76, 221, 245, 135, 251, 58, 243, 54, 59, 74, 230, 114, 92, 168, 123, 209, 60, 105, 107, 16, 206, 221, 242, 111,
        22, 30, 203, 8, 34, 86, 91, 77, 58, 113, 18, 134, 57, 92, 40, 31,
    ];
    let input3: [u8; 64] = [
        43, 147, 160, 179, 139, 127, 185, 64, 91, 10, 234, 203, 29, 51, 129, 173, 17, 12, 71, 214, 2, 64, 70, 255, 98,
        234, 131, 251, 72, 158, 175, 223, 4, 49, 19, 253, 76, 15, 236, 140, 240, 253, 108, 20, 249, 167, 164, 132, 108,
        138, 104, 10, 205, 255, 54, 21, 33, 62, 227, 79, 230, 66, 169, 237,
    ];

    println!("[input0]: {:?}", input0);
    //
    let data0 = CoinbasePuzzle::<Testnet3>::from_bytes_le(input0);
    println!("[data0]: {:?}", data0);
    // println!("[data0 hex]: {:#X}", data0);
    println!("BigInteger: {:?}", data0.0);

    assert_eq!(1, 1);
}

fn check_fr_ops<F: PrimeField>(a: F) -> F {
    a * a
}

#[test]
fn test_big_integer() {
    let a = BigInteger256::new([1, 2, 3, 4]);
    let arr = [
        123, 174, 25, 145, 165, 178, 187, 228, 35, 59, 182, 54, 166, 157, 152, 46, 247, 3, 224, 72, 183, 251, 215, 241,
        221, 153, 177, 207, 200, 102, 161, 0, 0,
    ];
    let arr2 = [
        123, 174, 25, 145, 165, 178, 187, 228, 35, 59, 182, 54, 166, 157, 152, 46, 247, 3, 224, 72, 183, 251, 215, 241,
        221, 153, 177, 207, 200, 102, 161, 0,
    ];
    let remaining_bytes: [u8; 33] = [
        253, 252, 225, 26, 13, 49, 85, 104, 253, 236, 19, 98, 4, 94, 217, 105, 11, 107, 242, 28, 155, 248, 224, 20,
        144, 41, 205, 131, 203, 238, 95, 29, 139,
    ];

    println!("a normal: {}", a);
    println!("a: {:?}", a);

    let bits = a.to_bits_le();
    println!("bits: {:?}", bits);

    let bytes = a.to_bytes_le();
    println!("bytes: {:?}", bytes);

    // let bignum : BigInteger256;
    // bignum::read_le(arr);
    // println!("bignum: {:?}", bignum);
    let b1 = BigUint::from_bytes_le(&arr2);
    println!("b1: {}", b1);
    // 出来了，很繁琐
    // 285171769418731151440234228452879219617491821202864546061759527540707929723

    println!("test biguint:");
    let arr3: [u8; 8] = [0x10, 0x00, 0x02, 0x00, 0x02, 0x01, 0x03, 0x00];
    let b2 = BigUint::from_bytes_le(&arr3);
    println!("b2: {}", b2);
    println!("b2: {:016X}", b2);
    // println!("b2: {:016X}", b2.0);
    // println!("b2: {:016X}", b2.1);
    // println!("b2: {:016X}", b2.2);
    // println!("b2: {:016X}", b2.3);

    println!("arr2 in Hex");
    for i in 0..arr2.len() {
        if (i % 8) == 0 && i != 0 {
            println!("");
        }
        print!("{:02X} ", arr2[i]);
    }
    //7B AE 19 91 A5 B2 BB E4
    //23 3B B6 36 A6 9D 98 2E
    //F7 03 E0 48 B7 FB D7 F1
    //DD 99 B1 CF C8 66 A1 00
    println!("");
    println!("arr2 in Hex Reverse order");
    for j in 0..arr2.len() {
        if (j % 8) == 0 && j != 0 {
            println!("");
        }
        print!("{:02X} ", arr2[31 - j]);
    }
    println!("");

    let B1 = BigInteger256::new([0xE4BBB2A5_9119AE7B, 0x2E989DA6_36B63B23, 0xF1D7FBB7_48E003F7, 0x00A166C8_CFB199DD]);
    println!("B1 normal : {}", B1);
    println!("B1 : {:?}", B1);

    let biarr = [0x7B, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    println!("\nbiarr: {}", BigUint::from_bytes_le(&biarr));
    let bi3 = BigInteger256::new([0x00000000_0000007B, 0x00000000_00000201, 0x00000000_00000000, 0x00000000_00000000]);
    println!("bi3: {}", bi3);
    println!("bi3: {:?}", bi3);
    for i in bi3.0.iter() {
        println!("{} {:0X}", i, *i);
    }

    let mut fp1 = Fr::from_bigint(B1).unwrap();
    // println!("fp1 normal: {}", fp1.ok_or(err).unwrap());
    println!("fp1: {:?}", fp1);
    println!("fp1, bytes le: {:?}", fp1.to_bigint().to_bytes_le());
    // fp1.AddAssign(1);
    // fp1.add(1); 不能加integer,
    // println!("fp1 size in bits {}", fp1.size_in_bits());
    // fp1 + 2;
    println!("fp1 is zero? {}", fp1.is_zero());
    let zero = Fr::zero();
    println!("fp zero: {:?}", zero);
    println!("fp1*fp1 : {:?}", check_fr_ops(fp1));

    let window_size = Fr::from(256u64);
    println!("window_size: {}", window_size);
    println!("window_size inspect: {:?}", window_size.to_bigint());
    println!("window_size in bytes le:{:?}", window_size.to_bigint().to_bytes_le());
    println!(" 。0 {}", window_size.0);
    println!(" debug {:?}", window_size.0);

    let window_size_2 = BigInteger256::from(256u64);
    let wdsize = Fr::from_bigint(window_size_2);
    println!("window_size: {:?}", wdsize.unwrap());
    println!("window_size inspect: {:?}", wdsize.unwrap().to_bigint());
    println!("{:?}", wdsize.unwrap().0);
    println!("window_size in bytes le:{:?}", wdsize.unwrap().to_bigint().to_bytes_le());

    // println!("window_size inspect: {:?}", wdsize.to_bigint());
    // println!("window_size in bytes le:{:?}", wdsize.to_bigint().to_bytes_le());
    // println!(" 。0 {}", wdsize.0);
    // println!(" debug {:?}", wdsize.0);

    // let test_B = BigInteger256::new([0,0,0,0x0000000000000001]);
    let test_B = BigInteger256::from(1);
    println!("test_B: {}", test_B);
    let test_B_int = test_B.to_biguint();
    println!("{:?}", test_B.0[0]);
    println!("{:?}", test_B.0[1]);
    println!("{:?}", test_B.0[2]);
    println!("{:?}", test_B.0[3]);
    println!("to bytes le: {:?}", test_B.to_bytes_le());
    println!("physically store sequence:");
    println!("{:016X}", test_B.0[0]);
    println!("{:016X}", test_B.0[1]);
    println!("{:016X}", test_B.0[2]);
    println!("{:016X}", test_B.0[3]);

    // println!(("test_B {:?}", test_B.to_bigint()));

    for byte in remaining_bytes {
        fp1 = fp1 * window_size;
        fp1 = fp1 + Fr::from(byte);
    }
    println!("res at end: {}", fp1);
    println!("res at end: {:?}", fp1);

    assert_eq!(1, 1);
}
