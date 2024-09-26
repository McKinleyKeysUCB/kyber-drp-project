
use crate::math::poly::Poly;
use crate::math::vector::Vector;
use crate::util::serializable::Serializable;

pub struct Ciphertext<const N: usize, const R: usize, const Q: u32> {
	pub u: Vector<Poly<N, Q, 1>, R>,
	pub v: Poly<N, Q, 1>,
}
impl<const N: usize, const R: usize, const Q: u32>
	Ciphertext<N, R, Q>
{
	pub fn serialize(&self) -> Vec<bool> {
		let mut result = vec![];
		result.extend(self.u.serialize().iter());
		result.extend(self.v.serialize().iter());
		result
	}
	pub fn deserialize<'a, I>(iter: &mut I) -> Option<Self>
	where
		I: Iterator<Item = &'a bool>
	{
		let Some(u) = Vector::deserialize(iter) else {
			return None;
		};
		let Some(v) = Poly::deserialize(iter) else {
			return None;
		};
		Some(Self { u, v })
	}
}
