
use crate::math::{matrix::Matrix, ntt::NTT, vector::Vector};

pub struct EncryptKey<const N: usize, const R: usize, const C: usize, const Q: u32> {
	// pub a: Matrix<Poly<N, Q, 1>, R, C>,
	// pub t: Vector<Poly<N, Q, 1>, R>,
	pub a: Matrix<NTT, R, C>,
	pub t: Vector<NTT, R>,
}
