
use crate::math::{matrix::Matrix, poly::Poly, vector::Vector};

pub struct EncryptKey<const N: usize, const R: usize, const C: usize, const Q: u32> {
	pub a: Matrix<Poly<N, Q>, R, C>,
	pub t: Vector<Poly<N, Q>, R>,
}
