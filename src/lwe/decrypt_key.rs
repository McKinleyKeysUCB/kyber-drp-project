
use crate::math::{qint::QInt, vector::Vector};

pub struct DecryptKey<const N: usize, const Q: u32> {
	pub s: Vector<QInt<Q>, N>,
}
