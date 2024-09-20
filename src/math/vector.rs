
use crate::math::ring::{Ring, RingOps};
use crate::util::serializable::Serializable;
use std::ops::{Add, Mul};

pub struct Vector<T, const N: usize> where T: Ring, for<'a> &'a T: RingOps<T> {
	pub data: [T; N],
}
impl<T, const N: usize>
	Serializable
	for Vector<T, N>
	where T: Serializable + Ring, for<'a> &'a T: RingOps<T>
{
	fn serialize(&self) -> Vec<bool> {
		let mut result = vec![];
		for value in &self.data {
			result.extend(value.serialize().iter());
		}
		result
	}
	fn deserialize<'a, I>(iter: &mut I) -> Option<Self>
	where
		I: Iterator<Item = &'a bool>
	{
		std::array::try_from_fn(|_| T::deserialize(iter))
			.map(|data| Self { data })
	}
}

impl<T, const N: usize>
	std::fmt::Display
	for Vector<T, N>
	where T: Ring + std::fmt::Display, for<'a> &'a T: RingOps<T>
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

impl<T, const N: usize>
	Vector<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	fn add_impl(&self, rhs: &Vector<T, N>) -> Vector<T, N> {
		Vector {
			data: std::array::from_fn(|i| &self.data[i] + &rhs.data[i]),
		}
	}
}
impl<T, const N: usize>
	Add<&Vector<T, N>>
	for &Vector<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = Vector<T, N>;
	fn add(self, rhs: &Vector<T, N>) -> Self::Output {
		self.add_impl(rhs)
	}
}
impl<T, const N: usize>
	Add<&Vector<T, N>>
	for Vector<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = Vector<T, N>;
	fn add(self, rhs: &Vector<T, N>) -> Self::Output {
		self.add_impl(rhs)
	}
}
impl<T, const N: usize>
	Add<Vector<T, N>>
	for &Vector<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = Vector<T, N>;
	fn add(self, rhs: Vector<T, N>) -> Self::Output {
		self.add_impl(&rhs)
	}
}
impl<T, const N: usize>
	Add<Vector<T, N>>
	for Vector<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = Vector<T, N>;
	fn add(self, rhs: Vector<T, N>) -> Self::Output {
		self.add_impl(&rhs)
	}
}

impl<T, const N: usize>
	Mul<&Vector<T, N>>
	for &Vector<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{	
	type Output = T;
	fn mul(self, rhs: &Vector<T, N>) -> Self::Output {
		(0 .. N).fold(T::zero(), |acc, i| acc + &self.data[i] * &rhs.data[i])
	}
}
