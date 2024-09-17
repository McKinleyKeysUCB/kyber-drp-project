
use crate::math::{qint::QUInt, vector::Vector};

pub struct Ciphertext<const N: usize, const Q: u32> {
	pub a: Vector<N, Q>,
	pub t: QUInt<Q>,
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
		let Some(t) = QUInt::deserialize(iter) else {
			return None;
		};
		Some(Self { a, t })
	}
}
