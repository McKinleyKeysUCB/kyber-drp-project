
use crate::math::{matrix::Matrix, qint::QInt, vector::Vector};

pub struct EncryptKey<const N: usize, const M: usize, const Q: u32> {
	pub a: Matrix<QInt<Q>, M, N>,
	pub t: Vector<QInt<Q>, M>,
}
