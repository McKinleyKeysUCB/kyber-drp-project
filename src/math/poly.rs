
use std::ops::{Add, Mul, Sub};

use super::{qint::QInt, ring::{Ring, RingOps}};

/// A member of `Z_Q[x]/(x^N + 1)`.
pub struct Poly<const N: usize, const Q: u32> {
	pub coefficients: [QInt<Q>; N],
}
impl<const N: usize, const Q: u32> Ring for Poly<N, Q> {
	fn zero() -> Self {
		let coefficients = std::array::from_fn(|_| QInt::zero());
		Self { coefficients }
	}
	fn one() -> Self {
		let coefficients = std::array::from_fn(|i| if i == 0 { QInt::one() } else { QInt::zero() });
		Self { coefficients }
	}
}
impl<const N: usize, const Q: u32> RingOps<Poly<N, Q>> for Poly<N, Q> {}
impl<const N: usize, const Q: u32> RingOps<Poly<N, Q>> for &Poly<N, Q> {}

impl<const N: usize, const Q: u32> Poly<N, Q>
{
	fn add_impl(&self, rhs: &Self) -> Self {
		let coefficients = std::array::from_fn(|i| self.coefficients[i] + rhs.coefficients[i]);
		Self { coefficients }
	}
	fn sub_impl(&self, rhs: &Self) -> Self {
		let coefficients = std::array::from_fn(|i| self.coefficients[i] - rhs.coefficients[i]);
		Self { coefficients }
	}
	fn mul_impl(&self, rhs: &Self) -> Self {
		let coefficients = std::array::from_fn(|i| {
			let positive = (0 ..= i).fold(QInt::zero(), |acc, j| {
				acc + self.coefficients[j] * rhs.coefficients[i - j]
			});
			let negative = (i + 1 .. N).fold(QInt::zero(), |acc, j| {
				acc + self.coefficients[j] * rhs.coefficients[i + N - j]
			});
			positive - negative
		});
		Self { coefficients }
	}
}

impl<const N: usize, const Q: u32> Add<Poly<N, Q>> for Poly<N, Q> {
	type Output = Poly<N, Q>;
	fn add(self, rhs: Poly<N, Q>) -> Self::Output {
		self.add_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32> Add<Poly<N, Q>> for &Poly<N, Q> {
	type Output = Poly<N, Q>;
	fn add(self, rhs: Poly<N, Q>) -> Self::Output {
		self.add_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32> Add<&Poly<N, Q>> for Poly<N, Q> {
	type Output = Poly<N, Q>;
	fn add(self, rhs: &Poly<N, Q>) -> Self::Output {
		self.add_impl(rhs)
	}
}
impl<const N: usize, const Q: u32> Add<&Poly<N, Q>> for &Poly<N, Q> {
	type Output = Poly<N, Q>;
	fn add(self, rhs: &Poly<N, Q>) -> Self::Output {
		self.add_impl(rhs)
	}
}
impl<const N: usize, const Q: u32> Sub<Poly<N, Q>> for Poly<N, Q> {
	type Output = Poly<N, Q>;
	fn sub(self, rhs: Poly<N, Q>) -> Self::Output {
		self.sub_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32> Sub<Poly<N, Q>> for &Poly<N, Q> {
	type Output = Poly<N, Q>;
	fn sub(self, rhs: Poly<N, Q>) -> Self::Output {
		self.sub_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32> Sub<&Poly<N, Q>> for Poly<N, Q> {
	type Output = Poly<N, Q>;
	fn sub(self, rhs: &Poly<N, Q>) -> Self::Output {
		self.sub_impl(rhs)
	}
}
impl<const N: usize, const Q: u32> Sub<&Poly<N, Q>> for &Poly<N, Q> {
	type Output = Poly<N, Q>;
	fn sub(self, rhs: &Poly<N, Q>) -> Self::Output {
		self.sub_impl(rhs)
	}
}
impl<const N: usize, const Q: u32> Mul<Poly<N, Q>> for Poly<N, Q> {
	type Output = Poly<N, Q>;
	fn mul(self, rhs: Poly<N, Q>) -> Self::Output {
		self.mul_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32> Mul<Poly<N, Q>> for &Poly<N, Q> {
	type Output = Poly<N, Q>;
	fn mul(self, rhs: Poly<N, Q>) -> Self::Output {
		self.mul_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32> Mul<&Poly<N, Q>> for Poly<N, Q> {
	type Output = Poly<N, Q>;
	fn mul(self, rhs: &Poly<N, Q>) -> Self::Output {
		self.mul_impl(rhs)
	}
}
impl<const N: usize, const Q: u32> Mul<&Poly<N, Q>> for &Poly<N, Q> {
	type Output = Poly<N, Q>;
	fn mul(self, rhs: &Poly<N, Q>) -> Self::Output {
		self.mul_impl(rhs)
	}
}


// --- Display ---

impl<const N: usize, const Q: u32>
	std::fmt::Display
	for Poly<N, Q>
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let formatted = self.coefficients.iter()
			.enumerate()
			.map(|(i, value)| {
				let result = value.to_string();
				match i {
					0 => result,
					1 => result + "x",
					_ => result + "x^" + &i.to_string(),
				}
			})
			.collect::<Vec<String>>()
			.join(" + ");
		write!(f, "{}", formatted)
	}
}
