
use crate::math::vector::Vector;

pub struct DecryptKey<const N: usize, const Q: u32> {
	pub s: Vector<N, Q>,
}
