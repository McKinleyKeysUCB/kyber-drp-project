
use crate::math::poly::Poly;

pub struct EncryptKey<const N: usize, const Q: u32> {
	pub a: Poly<N, Q>,
	pub t: Poly<N, Q>,
}
