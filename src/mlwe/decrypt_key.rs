
use crate::math::{poly::Poly, vector::Vector};

pub struct DecryptKey<const N: usize, const R: usize, const Q: u32> {
	pub s: Vector<Poly<N, Q, 1>, R>,
}
