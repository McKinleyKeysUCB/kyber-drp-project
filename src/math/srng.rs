
use crate::math::qint::{rem_nonneg, QInt};
use crate::math::bits::Bits;
use crate::math::vector::Vector;
use crate::math::matrix::Matrix;
use std::ops::{Range, RangeInclusive};
use rand::prelude::*;

pub struct SRng {
	rng: ThreadRng,
}
impl SRng {
	
	pub fn new() -> Self {
		Self {
			rng: rand::thread_rng(),
		}
	}
	
	pub fn gen_bits<const N: usize>(&mut self) -> Bits<N> {
		let mut data = [false; N];
		self.rng.fill(&mut data[..]);
		Bits { data }
	}
	pub fn gen_qint<const Q: u32>(&mut self) -> QInt<Q> {
		QInt::of_u32(self.rng.gen_range(0 .. Q))
	}
	pub fn gen_small_qint<const Q: u32>(&mut self, range: Range<i32>) -> QInt<Q> {
		QInt::of_u32(rem_nonneg::<Q>(self.rng.gen_range(range)))
	}
	pub fn gen_small_qint_inclusive<const Q: u32>(&mut self, range: RangeInclusive<i32>) -> QInt<Q> {
		QInt::of_u32(rem_nonneg::<Q>(self.rng.gen_range(range)))
	}
	pub fn gen_vector<const N: usize, const Q: u32>(&mut self) -> Vector<N, Q> {
		let data = std::array::from_fn(|_| self.gen_qint());
		Vector { data }
	}
	pub fn gen_small_vector<const N: usize, const Q: u32>(&mut self, range: Range<i32>) -> Vector<N, Q> {
		let data = std::array::from_fn(|_| self.gen_small_qint(range.clone()));
		Vector { data }
	}
	pub fn gen_small_vector_inclusive<const N: usize, const Q: u32>(&mut self, range: RangeInclusive<i32>) -> Vector<N, Q> {
		let data = std::array::from_fn(|_| self.gen_small_qint_inclusive(range.clone()));
		Vector { data }
	}
	pub fn gen_matrix<const R: usize, const C: usize, const Q: u32>(&mut self) -> Matrix<R, C, Q> {
		let rows = std::array::from_fn(|_| self.gen_vector());
		Matrix { rows }
	}
	
}
