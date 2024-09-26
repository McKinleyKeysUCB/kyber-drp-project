
use super::ring::{Ring, RingOps};
use std::ops::{Add, Mul, Sub};

#[derive(Clone)]
pub struct DirectSum<T, const N: usize> {
	elements: [T; N],
}
impl<T, const N: usize>
	Ring
	for DirectSum<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	fn zero() -> Self {
		let elements = std::array::from_fn(|_| T::zero());
		Self { elements }
	}
	fn one() -> Self {
		let elements = std::array::from_fn(|_| T::one());
		Self { elements }
	}
}
impl<T, const N: usize>
	RingOps<DirectSum<T, N>>
	for DirectSum<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{}
impl<T, const N: usize>
	RingOps<DirectSum<T, N>>
	for &DirectSum<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{}

impl<T, const N: usize>
	DirectSum<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	fn add_impl(&self, rhs: &Self) -> Self {
		let elements = std::array::from_fn(|i| &self.elements[i] + &rhs.elements[i]);
		Self { elements }
	}
	fn sub_impl(&self, rhs: &Self) -> Self {
		let elements = std::array::from_fn(|i| &self.elements[i] - &rhs.elements[i]);
		Self { elements }
	}
	fn mul_impl(&self, rhs: &Self) -> Self {
		let elements = std::array::from_fn(|i| &self.elements[i] * &rhs.elements[i]);
		Self { elements }
	}
}

impl<T, const N: usize>
	Add<DirectSum<T, N>>
	for DirectSum<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = DirectSum<T, N>;
	fn add(self, rhs: DirectSum<T, N>) -> Self::Output {
		self.add_impl(&rhs)
	}
}
impl<T, const N: usize>
	Add<DirectSum<T, N>>
	for &DirectSum<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = DirectSum<T, N>;
	fn add(self, rhs: DirectSum<T, N>) -> Self::Output {
		self.add_impl(&rhs)
	}
}
impl<T, const N: usize>
	Add<&DirectSum<T, N>>
	for DirectSum<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = DirectSum<T, N>;
	fn add(self, rhs: &DirectSum<T, N>) -> Self::Output {
		self.add_impl(rhs)
	}
}
impl<T, const N: usize>
	Add<&DirectSum<T, N>>
	for &DirectSum<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = DirectSum<T, N>;
	fn add(self, rhs: &DirectSum<T, N>) -> Self::Output {
		self.add_impl(rhs)
	}
}
impl<T, const N: usize> Sub<DirectSum<T, N>>
	for DirectSum<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = DirectSum<T, N>;
	fn sub(self, rhs: DirectSum<T, N>) -> Self::Output {
		self.sub_impl(&rhs)
	}
}
impl<T, const N: usize>
	Sub<DirectSum<T, N>>
	for &DirectSum<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = DirectSum<T, N>;
	fn sub(self, rhs: DirectSum<T, N>) -> Self::Output {
		self.sub_impl(&rhs)
	}
}
impl<T, const N: usize> Sub<&DirectSum<T, N>>
	for DirectSum<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = DirectSum<T, N>;
	fn sub(self, rhs: &DirectSum<T, N>) -> Self::Output {
		self.sub_impl(rhs)
	}
}
impl<T, const N: usize>
	Sub<&DirectSum<T, N>>
	for &DirectSum<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = DirectSum<T, N>;
	fn sub(self, rhs: &DirectSum<T, N>) -> Self::Output {
		self.sub_impl(rhs)
	}
}
impl<T, const N: usize>
	Mul<DirectSum<T, N>>
	for DirectSum<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = DirectSum<T, N>;
	fn mul(self, rhs: DirectSum<T, N>) -> Self::Output {
		self.mul_impl(&rhs)
	}
}
impl<T, const N: usize>
	Mul<DirectSum<T, N>>
	for &DirectSum<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = DirectSum<T, N>;
	fn mul(self, rhs: DirectSum<T, N>) -> Self::Output {
		self.mul_impl(&rhs)
	}
}
impl<T, const N: usize>
	Mul<&DirectSum<T, N>>
	for DirectSum<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = DirectSum<T, N>;
	fn mul(self, rhs: &DirectSum<T, N>) -> Self::Output {
		self.mul_impl(rhs)
	}
}
impl<T, const N: usize>
	Mul<&DirectSum<T, N>>
	for &DirectSum<T, N>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = DirectSum<T, N>;
	fn mul(self, rhs: &DirectSum<T, N>) -> Self::Output {
		self.mul_impl(rhs)
	}
}
