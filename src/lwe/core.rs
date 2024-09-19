
use crate::math::{qint::QInt, srng::SRng, vector::Vector};
use super::{ciphertext::Ciphertext, decrypt_key::DecryptKey, encrypt_key::EncryptKey};

pub fn keygen
	<const N: usize, const M: usize, const Q: u32>(
		rng: &mut SRng
	) -> (EncryptKey<N, M, Q>, DecryptKey<N, Q>)
{
	let s = rng.gen_vector::<N, Q>();
	let a = rng.gen_matrix::<M, N, Q>();
	let e = rng.gen_small_vector_inclusive::<M, Q>(-1 ..= 1);
	let t = &a * &s + &e;
	let encrypt_key = EncryptKey { a, t };
	let decrypt_key = DecryptKey { s };
	(encrypt_key, decrypt_key)
}

fn encrypt_bit
	<const N: usize, const M: usize, const Q: u32>(
		bit: bool,
		key: &EncryptKey<N, M, Q>,
		rng: &mut SRng
	) -> Ciphertext<N, Q>
{
	let mask = rng.gen_bits::<M>();
	let a_folded = mask.data.iter()
		.enumerate()
		.fold(Vector { data: [QInt::zero(); N] }, |acc, (i, value)| {
			if *value {
				acc + &key.a.rows[i]
			}
			else {
				acc
			}
		});
	let mut t_folded = mask.data.iter()
		.enumerate()
		.fold(QInt::zero(), |acc, (i, value)| {
			if *value {
				acc + key.t.data[i]
			}
			else {
				acc
			}
		});
	if bit {
		t_folded = t_folded + QInt::of_u32(Q / 2);
	}
	Ciphertext {
		a: a_folded,
		t: t_folded,
	}
}

fn decrypt_bit
	<const N: usize, const Q: u32>(
		ciphertext: &Ciphertext<N, Q>,
		key: &DecryptKey<N, Q>
	) -> bool
{
	let expected_value = (&ciphertext.a * &key.s);
	let dist = expected_value.dist(&ciphertext.t);
	dist.raw_value > Q / 4
}

pub fn encrypt
	<const N: usize, const M: usize, const Q: u32>(
		bits: &Vec<bool>,
		key: &EncryptKey<N, M, Q>,
		rng: &mut SRng
	) -> Vec<bool>
{
	let mut result = vec![];
	for bit in bits {
		let ciphertext = encrypt_bit(*bit, key, rng);
		result.extend(ciphertext.serialize().iter());
	}
	result
}

pub fn decrypt
	<const N: usize, const Q: u32>(
		bits: &Vec<bool>,
		key: &DecryptKey<N, Q>
	) -> Vec<bool>
{
	let mut result = vec![];
	let mut iter = bits.iter();
	loop {
		let Some(ciphertext) = Ciphertext::<N, Q>::deserialize(&mut iter) else {
			break;
		};
		let plaintext = decrypt_bit(&ciphertext, key);
		result.push(plaintext);
	}
	result
}
