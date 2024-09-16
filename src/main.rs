
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

fn main() {
	
	let mut rng = SRng::new();
	
	let (encrypt_key, decrypt_key) = keygen(&mut rng);
	
	let input = false;
	let ciphertext = encrypt(input, &encrypt_key, &mut rng);
	println!("Original ciphertext: {}, {}", ciphertext.a, ciphertext.t);
	let bits = ciphertext.serialize();
	println!("Bits: {:?}", bits);
	let base64 = bits.to_base64();
	println!("Result: {:?}", base64);
	let bits_decoded = Vec::<bool>::of_base64(&base64);
	println!("Decoded: {:?}", bits_decoded);
	let ciphertext_decoded = Ciphertext::<N, Q>::deserialize(&mut bits_decoded.into_iter());
	println!("Decoded ciphertext: {}, {}", ciphertext_decoded.a, ciphertext_decoded.t);
	
	// let input = false;
	// for _ in 0 .. 1_000_000 {
	// 	let ciphertext = encrypt(input, &encrypt_key, &mut rng);
	// 	let output = decrypt(&ciphertext, &decrypt_key);
	// 	if output != input {
	// 		println!("Failure");
	// 	}
	// }
}
