
use crate::math::{matrix::Matrix, vector::Vector};

pub struct EncryptKey<const N: usize, const M: usize, const Q: u32> {
	pub a: Matrix<M, N, Q>,
	pub t: Vector<M, Q>,
}
