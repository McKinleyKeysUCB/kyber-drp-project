
use crate::math::qint::QUInt;
use std::ops::Add;
use std::ops::Mul;

pub struct Vector<const N: usize, const Q: u32> {
	pub data: [QUInt<Q>; N],
}
impl<const N: usize, const Q: u32> Vector<N, Q> {
	pub fn serialize(&self) -> Vec<bool> {
		let mut result = vec![];
		for value in self.data {
			result.extend(value.serialize().iter());
		}
		result
	}
	pub fn deserialize<I>(iter: &mut I) -> Self
	where
		I: Iterator<Item = bool>
	{
		Self {
			data: std::array::from_fn(|_| QUInt::deserialize(iter))
		}
	}
}

impl<const N: usize, const Q: u32>
	std::fmt::Display
	for Vector<N, Q>
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let formatted = self.data
			.iter()
			.map(|value| value.to_string())
			.collect::<Vec<String>>()
			.join(", ");
		write!(f, "[{}]", formatted)
	}
}

impl<const N: usize, const Q: u32> Vector<N, Q> {
	fn add_impl(&self, rhs: &Vector<N, Q>) -> Vector<N, Q> {
		Vector {
			data: std::array::from_fn(|i| self.data[i] + rhs.data[i]),
		}
	}
}
impl<const N: usize, const Q: u32>
	Add<&Vector<N, Q>>
	for &Vector<N, Q>
{
	type Output = Vector<N, Q>;
	fn add(self, rhs: &Vector<N, Q>) -> Self::Output {
		self.add_impl(rhs)
	}
}
impl<const N: usize, const Q: u32>
	Add<&Vector<N, Q>>
	for Vector<N, Q>
{
	type Output = Vector<N, Q>;
	fn add(self, rhs: &Vector<N, Q>) -> Self::Output {
		self.add_impl(rhs)
	}
}
impl<const N: usize, const Q: u32>
	Add<Vector<N, Q>>
	for &Vector<N, Q>
{
	type Output = Vector<N, Q>;
	fn add(self, rhs: Vector<N, Q>) -> Self::Output {
		self.add_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32>
	Add<Vector<N, Q>>
	for Vector<N, Q>
{
	type Output = Vector<N, Q>;
	fn add(self, rhs: Vector<N, Q>) -> Self::Output {
		self.add_impl(&rhs)
	}
}

impl<const N: usize, const Q: u32>
	Mul<&Vector<N, Q>>
	for &Vector<N, Q>
{	
	type Output = QUInt<Q>;
	
	fn mul(self, rhs: &Vector<N, Q>) -> Self::Output {
		(0 .. N).fold(QUInt::zero(), |acc, i| acc + self.data[i] * rhs.data[i])
	}	
}
