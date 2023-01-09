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
use aleo_std::{start_timer, end_timer};
use console::{account::*, network::Testnet3};
use snarkvm_utilities::Uniform;

use rand::RngCore;

use std::time::{Duration, Instant};


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
fn test_cuda_parallel(){
    let start = Instant::now();

    println!("test cuda parallel");

    let duration = start.elapsed();
    println!("Time elapsed in expensive_function() is: {:?}", duration);
    assert!(1 == 1);
}

#[test]
fn test_polynomial(){
    println!("test_polynomial()");
    // let mut rng = TestRng::default();

    let max_degree = 1 << 15;
    let max_config = PuzzleConfig { degree: max_degree };
    let srs = CoinbasePuzzle::<Testnet3>::setup(max_config).unwrap();

    let log_degree = 2;
    let degree = (1 << log_degree) - 1;
    let config = PuzzleConfig { degree };
    let puzzle = CoinbasePuzzle::<Testnet3>::trim(&srs, config).unwrap();
    let epoch_number =  0x11ABAEAA;
    // let epoch_block_hash = "ab1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq5g436j";
    // let epoch_challenge = EpochChallenge::new(epoch_number, Default::default(), degree).unwrap();
    // default value is data , F::zero()

    println!("Begin EpochChallenge::new()");
    let epoch_challenge = EpochChallenge::new(epoch_number,Default::default() , degree).unwrap();
    // 这里会生成一个product_domain, 使用到的算法，和后续是一样的!

    println!("epoch_number: {:#X}", epoch_challenge.epoch_number());
    println!("epoch_block_hash: {}", epoch_challenge.epoch_block_hash());
    println!("epoch_polynomial: {:?}", epoch_challenge.epoch_polynomial());
    println!("epoch_polynomail_evaluations: {:?}", epoch_challenge.epoch_polynomial_evaluations());

    // let private_key = PrivateKey::<Testnet3>::new(&mut rng).unwrap();
    let private_key = PrivateKey::<Testnet3>::from_str("APrivateKey1zkp686TthAY2rhCzhLwDZEeYkxA33vNwC2yB8va7FDP6yEM").unwrap();
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
fn test_blake2b512(){
    println!("test_blake2b512()");
    let max_degree = 1 << 15;
    let max_config = PuzzleConfig { degree: max_degree };
    let srs = CoinbasePuzzle::<Testnet3>::setup(max_config).unwrap();

    let log_degree = 2;
    let degree = (1 << log_degree) - 1;
    let config = PuzzleConfig { degree };
    let puzzle = CoinbasePuzzle::<Testnet3>::trim(&srs, config).unwrap();
    let epoch_number =  0x11ABAEAA;

 
    let epoch_challenge = EpochChallenge::<Testnet3>::new(epoch_number,Default::default() , degree).unwrap();

    println!("epoch_number: {:#X}", epoch_challenge.epoch_number());
    println!("epoch_block_hash: {}", epoch_challenge.epoch_block_hash());
    println!("epoch_polynomial: {:?}", epoch_challenge.epoch_polynomial());
    println!("epoch_polynomail_evaluations: {:?}", epoch_challenge.epoch_polynomial_evaluations());
    
    let private_key = PrivateKey::<Testnet3>::from_str("APrivateKey1zkp686TthAY2rhCzhLwDZEeYkxA33vNwC2yB8va7FDP6yEM").unwrap();
    //let private_key = "APrivateKey1zkp686TthAY2rhCzhLwDZEeYkxA33vNwC2yB8va7FDP6yEM";
    println!("private_key: {}", private_key);
    let address = Address::try_from(private_key).unwrap();
    println!("address: {}", address);
    //let nonce = u64::rand(&mut rng);
    let nonce: u64 = 0x11110000;
    println!("nonce: {:#X}", nonce);

    // let input = {
    //     let mut bytes = [0u8; 76];
    //     bytes[..4].copy_from_slice(&epoch_challenge.epoch_number().to_bytes_le()?);
    //     bytes[4..36].copy_from_slice(&epoch_challenge.epoch_block_hash().to_bytes_le());
    //     bytes[36..68].copy_from_slice(&address.to_bytes_le()?);
    //     bytes[68..].copy_from_slice(&nonce.to_le_bytes());
    //     bytes
    // };

    assert_eq!(1,1);
}