
use crate::math::poly::Poly;

pub struct EncryptKey<const N: usize, const Q: u32> {
	pub a: Poly<N, Q, 1>,
	pub t: Poly<N, Q, 1>,
}
