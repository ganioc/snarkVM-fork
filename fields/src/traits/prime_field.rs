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

use crate::{FftField, FieldError, FieldParameters, PoseidonDefaultField};
use snarkvm_utilities::{biginteger::BigInteger, cmp::min, str::FromStr, ToBytes, BigInteger256};

/// The interface for a prime field.
pub trait PrimeField:
    FftField<FftParameters = <Self as PrimeField>::Parameters> + PoseidonDefaultField + FromStr<Err = FieldError>
{
    /// Returns the field size in bits.
    const SIZE_IN_BITS: usize = Self::Parameters::MODULUS_BITS as usize;
    /// Returns the field capacity for data bits.
    const SIZE_IN_DATA_BITS: usize = Self::Parameters::CAPACITY as usize;

    type Parameters: FieldParameters<BigInteger = Self::BigInteger>;
    type BigInteger: BigInteger;

    /// Constructs a `PrimeField` element given a human-readable `Self::BigInteger`.
    fn from_bigint(repr: Self::BigInteger) -> Option<Self>;

    /// Returns a human-readable `Self::BigInteger` in the range `0..(Self::MODULUS - 1)`.
    fn to_bigint(&self) -> Self::BigInteger;

    /// Returns the decomposition of the scalar.
    fn decompose(
        &self,
        q1: &[u64; 4],
        q2: &[u64; 4],
        b1: Self,
        b2: Self,
        r128: Self,
        half_r: &[u64; 8],
    ) -> (Self, Self, bool, bool);

    /// Returns the field size in bits.
    fn size_in_bits() -> usize {
        Self::Parameters::MODULUS_BITS as usize
    }

    /// Returns the capacity size for data bits.
    fn size_in_data_bits() -> usize {
        Self::Parameters::CAPACITY as usize
    }

    /// Returns the modulus.
    fn modulus() -> Self::BigInteger {
        Self::Parameters::MODULUS
    }

    /// Returns the modulus minus one divided by two.
    fn modulus_minus_one_div_two() -> Self::BigInteger {
        Self::Parameters::MODULUS_MINUS_ONE_DIV_TWO
    }

    /// Returns the trace.
    fn trace() -> Self::BigInteger {
        Self::Parameters::T
    }

    /// Returns the trace minus one divided by two.
    fn trace_minus_one_div_two() -> Self::BigInteger {
        Self::Parameters::T_MINUS_ONE_DIV_TWO
    }

    /// Reads bytes in big-endian, and converts them to a field element.
    /// If the bytes are larger than the modulus, it will reduce them.
    fn from_bytes_be_mod_order(bytes: &[u8]) -> Self {
        println!("from_bytes_be_mod_order");
        println!("MODULUS_BITS: {}", Self::Parameters::MODULUS_BITS);
        let num_modulus_bytes = ((Self::Parameters::MODULUS_BITS + 7) / 8) as usize;
        println!("num_modulus_bytes: {}", num_modulus_bytes);

        let num_bytes_to_directly_convert = min(num_modulus_bytes - 1, bytes.len());
        println!("num_bytes_to_directly_convert: {}", num_bytes_to_directly_convert);

        let (leading_bytes, remaining_bytes) = bytes.split_at(num_bytes_to_directly_convert);
        println!("leading_bytes: {:?}", leading_bytes);
        println!("remaining_bytes: {:?}", remaining_bytes);
        // Copy the leading big-endian bytes directly into a field element.
        // The number of bytes directly converted must be less than the
        // number of bytes needed to represent the modulus, as we must begin
        // modular reduction once the data is of the same number of bytes as the modulus.
        let mut bytes_to_directly_convert = leading_bytes.to_vec();
        bytes_to_directly_convert.reverse();
        println!("bytes_to_directyl_convert: {:?}", bytes_to_directly_convert);
        
        // Guaranteed to not be None, as the input is less than the modulus size.
        let mut res = Self::from_random_bytes(&bytes_to_directly_convert).unwrap();
        println!("res from_random_bytes: {:?}", res);
        println!("res to_bytes_le, {:?}", res.to_bigint().to_bytes_le());
        println!("res bigint 0: {:?}", res.to_bigint());
        // let test_B = BigInteger256::from(res.to_bigint());


        // Update the result, byte by byte.
        // We go through existing field arithmetic, which handles the reduction.
        let window_size = Self::from(256u64);
        println!("window_size: {}", window_size);
        println!("u64:");
        println!("0, {:?}", window_size.to_bigint().to_bytes_le());
        // println!("1, {}", window_size.to_bigint());
        // println!("2, {}", window_size.to_bigint());
        // println!("3, {}", window_size.to_bigint());

        for byte in remaining_bytes{
            print!("{:?} ", Self::from(*byte));
        }
        println!("");

        for byte in remaining_bytes {
            // println!("self::from : {:?}", Self::from(*byte));
            res *= window_size;
            res += Self::from(*byte);
        }
        println!("res at end: {:?}", res);
        println!("res at end to bytes: {:?}", res.to_bigint().to_bytes_le());
        res
    }

    /// Reads bytes in little-endian, and converts them to a field element.
    /// If the bytes are larger than the modulus, it will reduce them.
    fn from_bytes_le_mod_order(bytes: &[u8]) -> Self {
        println!("from_bytes_le_mod_order()");

        let mut bytes_copy = bytes.to_vec();
        bytes_copy.reverse();
        println!("bytes_copy reverse: {:?}", bytes_copy);
        Self::from_bytes_be_mod_order(&bytes_copy)
    }
}
