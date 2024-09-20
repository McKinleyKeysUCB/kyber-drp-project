
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(adt_const_params)]
#![feature(cmp_minmax)]
#![feature(array_try_from_fn)]

#![allow(unused_parens)]
#![allow(dead_code)]

mod base64;
mod lwe;
mod math;
mod mlwe;
mod rlwe;
mod util;

use base64::Base64Convertible;
use mlwe::core::{decrypt, encrypt, keygen};
use math::srng::SRng;

const N: usize = 8;
const M: usize = 3;
const Q: u32 = 71;

fn string_to_bits(message: &str) -> Vec<bool> {
	let mut result = vec![];
	for ch in message.chars() {
		let mut byte = ch as u8;
		for _ in 0 .. 8 {
			result.push(byte % 2 == 1);
			byte /= 2;
		}
	}
	result
}
fn string_of_bits(bits: &Vec<bool>) -> String {
	let mut result = String::new();
	for start_index in (0 .. bits.len()).step_by(8) {
		let end_index = std::cmp::min(start_index + 8, bits.len());
		let slice = &bits[start_index .. end_index];
		let mut total = 0u32;
		let mut p = 1;
		for bit in slice {
			if *bit {
				total += p;
			}
			p *= 2;
		}
		result.push(total as u8 as char);
	}
	result
}

fn main() {
	
	let mut rng = SRng::new();
	
	let (encrypt_key, decrypt_key) = keygen(&mut rng);
	
	let message = "Hello there. This is a really long message that takes several lines. Will it all be decrypted correctly?";
	let message_bits = string_to_bits(&message);
	let cipher = encrypt(&message_bits, &encrypt_key, &mut rng);
	let base64 = cipher.to_base64();
	println!("Base64: {:?}", base64);
	let cipher_deserialized = Vec::<bool>::of_base64(&base64);
	let result_bits = decrypt(&cipher_deserialized, &decrypt_key);
	let result = string_of_bits(&result_bits);
	println!("Result: {:?}", result);
}
