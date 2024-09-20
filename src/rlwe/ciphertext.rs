
use crate::math::poly::Poly;
use crate::util::serializable::Serializable;

pub struct Ciphertext<const N: usize, const Q: u32> {
	pub u: Poly<N, Q>,
	pub v: Poly<N, Q>,
}
impl<const N: usize, const Q: u32>
	Ciphertext<N, Q>
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
		let Some(u) = Poly::deserialize(iter) else {
			return None;
		};
		let Some(v) = Poly::deserialize(iter) else {
			return None;
		};
		Some(Self { u, v })
	}
}
