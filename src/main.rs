
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(adt_const_params)]
#![feature(cmp_minmax)]

#![allow(unused_parens)]
#![allow(dead_code)]

mod ciphertext;
mod encrypt_key;
mod decrypt_key;
mod math;

use ciphertext::Ciphertext;
use decrypt_key::DecryptKey;
use encrypt_key::EncryptKey;
use math::qint::QUInt;
use math::srng::SRng;
use math::vector::Vector;
use base64::alphabet::STANDARD as BASE64_ALPHABET;

const N: usize = 4;
const M: usize = 3;
const Q: u32 = 23;

fn keygen(rng: &mut SRng) -> (EncryptKey<N, M, Q>, DecryptKey<N, Q>) {
	let s = rng.gen_vector::<N, Q>();
	let a = rng.gen_matrix::<M, N, Q>();
	let e = rng.gen_small_vector_inclusive::<M, Q>(-1 ..= 1);
	let t = &a * &s + &e;
	let encrypt_key = EncryptKey { a, t };
	let decrypt_key = DecryptKey { s };
	(encrypt_key, decrypt_key)
}

fn encrypt(bit: bool, key: &EncryptKey<N, M, Q>, rng: &mut SRng) -> Ciphertext<N, Q> {
	let mask = rng.gen_bits::<M>();
	let a_folded = mask.data.iter()
		.enumerate()
		.fold(Vector { data: [QUInt::zero(); N] }, |acc, (i, value)| {
			if *value {
				acc + &key.a.rows[i]
			}
			else {
				acc
			}
		});
	let mut t_folded = mask.data.iter()
		.enumerate()
		.fold(QUInt::zero(), |acc, (i, value)| {
			if *value {
				acc + key.t.data[i]
			}
			else {
				acc
			}
		});
	if bit {
		t_folded = t_folded + QUInt::of_u32(Q / 2);
	}
	Ciphertext {
		a: a_folded,
		t: t_folded,
	}
}
fn decrypt(ciphertext: &Ciphertext<N, Q>, key: &DecryptKey<N, Q>) -> bool {
	let expected_value = (&ciphertext.a * &key.s);
	let dist = expected_value.dist(&ciphertext.t);
	dist.raw_value > Q / 4
}

trait Base64Convertible {
	fn to_base64(&self) -> String;
	fn of_base64(base64: &str) -> Self;
}
impl Base64Convertible for Vec<bool> {
	fn to_base64(&self) -> String {
		let mut result = String::new();
		for start_index in (0 .. self.len()).step_by(6) {
			let end_index = std::cmp::min(start_index + 6, self.len());
			let slice = &self[start_index .. end_index];
			let mut total = 0usize;
			let mut p = 1;
			for bit in slice {
				if *bit {
					total += p;
				}
				p *= 2;
			}
			result.push(BASE64_ALPHABET.as_str().chars().nth(total).unwrap());
		}
		result
	}
	fn of_base64(base64: &str) -> Self {
		let mut bools = vec![];
		for ch in base64.chars() {
			let mut index = BASE64_ALPHABET.as_str()
				.chars()
				.position(|x| x == ch)
				.unwrap();
			for _ in 0 .. 6 {
				bools.push(index % 2 == 1);
				index /= 2;
			}
		}
		bools
	}
}

fn encrypt_bits(bits: &Vec<bool>, key: &EncryptKey<N, M, Q>, rng: &mut SRng) -> Vec<bool> {
	let mut result = vec![];
	for bit in bits {
		let ciphertext = encrypt(*bit, key, rng);
		result.extend(ciphertext.serialize().iter());
	}
	result
}
fn decrypt_bits(bits: &Vec<bool>, key: &DecryptKey<N, Q>) -> Vec<bool> {
	let mut result = vec![];
	let mut iter = bits.iter();
	loop {
		let Some(ciphertext) = Ciphertext::<N, Q>::deserialize(&mut iter) else {
			break;
		};
		let plaintext = decrypt(&ciphertext, key);
		result.push(plaintext);
	}
	result
}

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
	
	let message = "Hello";
	let message_bits = string_to_bits(&message);
	let cipher = encrypt_bits(&message_bits, &encrypt_key, &mut rng);
	let base64 = cipher.to_base64();
	println!("Base64: {:?}", base64);
	let cipher_deserialized = Vec::<bool>::of_base64(&base64);
	let result_bits = decrypt_bits(&cipher_deserialized, &decrypt_key);
	let result = string_of_bits(&result_bits);
	println!("Result: {:?}", result);
}
