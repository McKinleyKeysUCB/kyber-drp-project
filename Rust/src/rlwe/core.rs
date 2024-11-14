
use crate::math::{bits::Bits, poly::Poly, qint::QInt, ring::Ring, srng::SRng};
use super::{ciphertext::Ciphertext, decrypt_key::DecryptKey, encrypt_key::EncryptKey};

pub fn keygen
	<const N: usize, const Q: u32>(
		rng: &mut SRng
	) -> (EncryptKey<N, Q>, DecryptKey<N, Q>)
{
	let s = rng.gen_small_poly_inclusive::<N, Q, 1>(&(-1 ..= 1));
	let a = rng.gen_poly::<N, Q, 1>();
	let e = rng.gen_small_poly_inclusive::<N, Q, 1>(&(-1 ..= 1));
	let t = &a * &s + &e;
	let encrypt_key = EncryptKey { a, t };
	let decrypt_key = DecryptKey { s };
	(encrypt_key, decrypt_key)
}

fn encrypt_chunk
	<const N: usize, const Q: u32>(
		bits: Bits<N>,
		key: &EncryptKey<N, Q>,
		rng: &mut SRng
	) -> Ciphertext<N, Q>
{
	let m = Poly { coefficients: std::array::from_fn(|i| if bits.data[i] { QInt::one() } else { QInt::zero() }) };
	let r = rng.gen_small_poly_inclusive::<N, Q, 1>(&(-1 ..= 1));
	let e1 = rng.gen_small_poly_inclusive::<N, Q, 1>(&(-1 ..= 1));
	let e2 = rng.gen_small_poly_inclusive::<N, Q, 1>(&(-1 ..= 1));
	let u = &key.a * &r + &e1;
	let v = &key.t * &r + &e2 + QInt::half() * m;
	Ciphertext { u, v }
}

fn decrypt_chunk
	<const N: usize, const Q: u32>(
		ciphertext: &Ciphertext<N, Q>,
		key: &DecryptKey<N, Q>
	) -> Bits<N>
{
	let expected_value = &ciphertext.v - &ciphertext.u * &key.s;
	Bits {
		data: expected_value.coefficients.map(|c| {
			let dist = c.dist(&QInt::zero());
			dist.raw_value > Q / 4
		}),
	}
}

pub fn split_into_chunks<const N: usize>(bits: &Vec<bool>) -> Vec<Bits<N>> {
	if N == 0 {
		panic!();
	}
	let mut chunks = vec![];
	let mut current_chunk = [false; N];
	let mut i = 0;
	for bit in bits {
		current_chunk[i] = *bit;
		i += 1;
		if i == N {
			chunks.push(Bits { data: current_chunk });
			i = 0;
		}
	}
	// If we have a partially filled chunk
	if i > 0 {
		chunks.push(Bits { data: current_chunk });
	}
	chunks
}

pub fn encrypt
	<const N: usize, const Q: u32>(
		bits: &Vec<bool>,
		key: &EncryptKey<N, Q>,
		rng: &mut SRng
	) -> Vec<bool>
{
	let mut result = vec![];
	for chunk in split_into_chunks(bits) {
		let ciphertext = encrypt_chunk(chunk, key, rng);
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
		let plaintext = decrypt_chunk(&ciphertext, key);
		result.extend(plaintext.data.iter());
	}
	result
}
