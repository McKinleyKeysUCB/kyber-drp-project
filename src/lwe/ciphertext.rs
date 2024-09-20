
use crate::math::{qint::QInt, vector::Vector};
use crate::util::serializable::Serializable;

pub struct Ciphertext<const N: usize, const Q: u32> {
	pub a: Vector<QInt<Q>, N>,
	pub t: QInt<Q>,
}
impl<const N: usize, const Q: u32>
	Ciphertext<N, Q>
{
	pub fn serialize(&self) -> Vec<bool> {
		let mut result = vec![];
		result.extend(self.a.serialize().iter());
		result.extend(self.t.serialize().iter());
		result
	}
	pub fn deserialize<'a, I>(iter: &mut I) -> Option<Self>
	where
		I: Iterator<Item = &'a bool>
	{
		let Some(a) = Vector::deserialize(iter) else {
			return None;
		};
		let Some(t) = QInt::deserialize(iter) else {
			return None;
		};
		Some(Self { a, t })
	}
}
