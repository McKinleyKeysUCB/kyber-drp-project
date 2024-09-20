
use crate::math::poly::Poly;

pub struct DecryptKey<const N: usize, const Q: u32> {
	pub s: Poly<N, Q>,
}
