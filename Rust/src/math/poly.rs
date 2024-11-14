
use crate::util::serializable::Serializable;
use super::{qint::QInt, ring::{Ring, RingOps}};
use std::ops::{Add, Div, Mul, Sub};

/// A member of `Z_Q[x]/(x^N + C)`.
/// 
/// Ideally, we want the signature to be:
/// ```
/// pub struct Poly<T, const N: usize, const C: T>
/// ```
/// but Rust doesn't yet support const parameters that depend on generic types.
#[derive(Clone, PartialEq, Debug)]
pub struct Poly<const N: usize, const Q: u32, const C: u32> {
	pub coefficients: [QInt<Q>; N],
}

impl<const N: usize, const Q: u32, const C: u32> Ring for Poly<N, Q, C> {
	fn zero() -> Self {
		let coefficients = std::array::from_fn(|_| QInt::zero());
		Self { coefficients }
	}
	fn one() -> Self {
		let coefficients = std::array::from_fn(|i| if i == 0 { QInt::one() } else { QInt::zero() });
		Self { coefficients }
	}
}
impl<const N: usize, const Q: u32, const C: u32>
	RingOps<Poly<N, Q, C>>
	for Poly<N, Q, C>
{}
impl<const N: usize, const Q: u32, const C: u32>
	RingOps<Poly<N, Q, C>>
	for &Poly<N, Q, C>
{}

impl<const N: usize, const Q: u32, const C: u32> Poly<N, Q, C> {
	pub fn add(lhs: &Self, rhs: &Self) -> Self {
		let coefficients = std::array::from_fn(|i| lhs.coefficients[i] + rhs.coefficients[i]);
		Self { coefficients }
	}
	pub fn sub(lhs: &Self, rhs: &Self) -> Self {
		let coefficients = std::array::from_fn(|i| lhs.coefficients[i] - rhs.coefficients[i]);
		Self { coefficients }
	}
	pub fn mul(lhs: &Self, rhs: &Self) -> Self {
		let coefficients = std::array::from_fn(|i| {
			let positive = (0 ..= i).fold(QInt::zero(), |acc, j| {
				acc + lhs.coefficients[j] * rhs.coefficients[i - j]
			});
			let negative = (i + 1 .. N).fold(QInt::zero(), |acc, j| {
				acc + lhs.coefficients[j] * rhs.coefficients[i + N - j] * QInt::of_u32(C)
			});
			positive - negative
		});
		Self { coefficients }
	}
	pub fn div(lhs: &Self, rhs: &Self) -> Self {
		match (0 .. N).rev().find(|i| rhs.coefficients[*i] != QInt::zero()) {
			None => panic!("rhs is zero"),
			Some(rhs_leading_index) => {
				let rhs_leading_coefficient = rhs.coefficients[rhs_leading_index];
				let mut lhs_coefficients = lhs.coefficients.clone();
				let mut result_coefficients = [QInt::zero(); N];
				for i in (rhs_leading_index .. N).rev() {
					let c = lhs_coefficients[i] / rhs_leading_coefficient;
					result_coefficients[i - rhs_leading_index] = c;
					for j in 0 ..= rhs_leading_index {
						lhs_coefficients[i - (rhs_leading_index - j)] -= c * rhs.coefficients[j];
					}
				}
				Self { coefficients: result_coefficients }
			}
		}
	}
	pub fn mul_scalar(lhs: &Self, rhs: &QInt<Q>) -> Self {
		let coefficients = lhs.coefficients.map(|c| c * rhs);
		Self { coefficients }
	}
	pub fn div_scalar(lhs: &Self, rhs: &QInt<Q>) -> Self {
		Self::mul_scalar(lhs, &rhs.inv())
	}
	fn add_impl(&self, rhs: &Self) -> Self {
		Self::add(self, rhs)
	}
	fn sub_impl(&self, rhs: &Self) -> Self {
		Self::sub(self, rhs)
	}
	fn mul_impl(&self, rhs: &Self) -> Self {
		Self::mul(self, rhs)
	}
	fn div_impl(&self, rhs: &Self) -> Self {
		Self::div(self, rhs)
	}
	fn mul_scalar_impl(&self, rhs: &QInt<Q>) -> Self {
		Self::mul_scalar(self, rhs)
	}
	fn div_scalar_impl(&self, rhs: &QInt<Q>) -> Self {
		Self::div_scalar(self, rhs)
	}
	pub fn rem<const M: usize, const D: u32>(&self) -> Poly<M, Q, D> {
		assert!(N >= M);
		let mut coefficients = self.coefficients.clone();
		for i in (M .. N).rev() {
			coefficients[i - M] -= &coefficients[i] * QInt::of_u32(D);
			coefficients[i] = QInt::zero();
		}
		let sliced_coefficients = std::array::from_fn(|i| coefficients[i]);
		Poly { coefficients: sliced_coefficients }
	}
	pub fn embedded<const M: usize, const D: u32>(&self) -> Poly<M, Q, D> {
		assert!(M >= N);
		let coefficients = std::array::from_fn(|i| if i < N { self.coefficients[i] } else { QInt::zero() });
		Poly { coefficients }
	}
}

impl<const Q: u32, const C: u32> Poly<2, Q, C> {
	pub fn inv(&self) -> Poly<2, Q, C> {
		assert_ne!(*self, Self::zero());
		let c = QInt::of_u32(C);
		let b = self.coefficients[0];
		let a = self.coefficients[1];
		if a == QInt::zero() {
			let coefficients = [
				b.inv(),
				QInt::zero(),
			];
			Poly { coefficients }
		}
		else {
			let a_inv = a.inv();
			let d = a_inv * a_inv * b * b + c;
			let d_inv = (-d).inv();
			let coefficients = [
				-b * a_inv * a_inv * d_inv,
				a_inv * d_inv,
			];
			Poly { coefficients }
		}
	}
}

impl<const N: usize, const Q: u32, const C: u32> Add<Poly<N, Q, C>> for Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn add(self, rhs: Poly<N, Q, C>) -> Self::Output {
		self.add_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Add<Poly<N, Q, C>> for &Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn add(self, rhs: Poly<N, Q, C>) -> Self::Output {
		self.add_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Add<&Poly<N, Q, C>> for Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn add(self, rhs: &Poly<N, Q, C>) -> Self::Output {
		self.add_impl(rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Add<&Poly<N, Q, C>> for &Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn add(self, rhs: &Poly<N, Q, C>) -> Self::Output {
		self.add_impl(rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Sub<Poly<N, Q, C>> for Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn sub(self, rhs: Poly<N, Q, C>) -> Self::Output {
		self.sub_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Sub<Poly<N, Q, C>> for &Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn sub(self, rhs: Poly<N, Q, C>) -> Self::Output {
		self.sub_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Sub<&Poly<N, Q, C>> for Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn sub(self, rhs: &Poly<N, Q, C>) -> Self::Output {
		self.sub_impl(rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Sub<&Poly<N, Q, C>> for &Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn sub(self, rhs: &Poly<N, Q, C>) -> Self::Output {
		self.sub_impl(rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Mul<Poly<N, Q, C>> for Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn mul(self, rhs: Poly<N, Q, C>) -> Self::Output {
		self.mul_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Mul<Poly<N, Q, C>> for &Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn mul(self, rhs: Poly<N, Q, C>) -> Self::Output {
		self.mul_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Mul<&Poly<N, Q, C>> for Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn mul(self, rhs: &Poly<N, Q, C>) -> Self::Output {
		self.mul_impl(rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Mul<&Poly<N, Q, C>> for &Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn mul(self, rhs: &Poly<N, Q, C>) -> Self::Output {
		self.mul_impl(rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Div<Poly<N, Q, C>> for Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn div(self, rhs: Poly<N, Q, C>) -> Self::Output {
		self.div_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Div<Poly<N, Q, C>> for &Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn div(self, rhs: Poly<N, Q, C>) -> Self::Output {
		self.div_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Div<&Poly<N, Q, C>> for Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn div(self, rhs: &Poly<N, Q, C>) -> Self::Output {
		self.div_impl(rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Div<&Poly<N, Q, C>> for &Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn div(self, rhs: &Poly<N, Q, C>) -> Self::Output {
		self.div_impl(rhs)
	}
}


// --- Scalar Multiplication ---

impl<const N: usize, const Q: u32, const C: u32> Mul<QInt<Q>> for Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn mul(self, rhs: QInt<Q>) -> Self::Output {
		self.mul_scalar_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Mul<QInt<Q>> for &Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn mul(self, rhs: QInt<Q>) -> Self::Output {
		self.mul_scalar_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Mul<&QInt<Q>> for Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn mul(self, rhs: &QInt<Q>) -> Self::Output {
		self.mul_scalar_impl(rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Mul<&QInt<Q>> for &Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn mul(self, rhs: &QInt<Q>) -> Self::Output {
		self.mul_scalar_impl(rhs)
	}
}

impl<const N: usize, const Q: u32, const C: u32> Mul<Poly<N, Q, C>> for QInt<Q> {
	type Output = Poly<N, Q, C>;
	fn mul(self, rhs: Poly<N, Q, C>) -> Self::Output {
		rhs.mul_scalar_impl(&self)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Mul<Poly<N, Q, C>> for &QInt<Q> {
	type Output = Poly<N, Q, C>;
	fn mul(self, rhs: Poly<N, Q, C>) -> Self::Output {
		rhs.mul_scalar_impl(self)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Mul<&Poly<N, Q, C>> for QInt<Q> {
	type Output = Poly<N, Q, C>;
	fn mul(self, rhs: &Poly<N, Q, C>) -> Self::Output {
		rhs.mul_scalar_impl(&self)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Mul<&Poly<N, Q, C>> for &QInt<Q> {
	type Output = Poly<N, Q, C>;
	fn mul(self, rhs: &Poly<N, Q, C>) -> Self::Output {
		rhs.mul_scalar_impl(self)
	}
}


// --- Scalar Division ---

impl<const N: usize, const Q: u32, const C: u32> Div<QInt<Q>> for Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn div(self, rhs: QInt<Q>) -> Self::Output {
		self.div_scalar_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Div<QInt<Q>> for &Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn div(self, rhs: QInt<Q>) -> Self::Output {
		self.div_scalar_impl(&rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Div<&QInt<Q>> for Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn div(self, rhs: &QInt<Q>) -> Self::Output {
		self.div_scalar_impl(rhs)
	}
}
impl<const N: usize, const Q: u32, const C: u32> Div<&QInt<Q>> for &Poly<N, Q, C> {
	type Output = Poly<N, Q, C>;
	fn div(self, rhs: &QInt<Q>) -> Self::Output {
		self.div_scalar_impl(rhs)
	}
}


// --- Display ---

impl<const N: usize, const Q: u32, const C: u32>
	std::fmt::Display
	for Poly<N, Q, C>
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let formatted = if self.coefficients.iter().all(|c| c == &QInt::zero()) {
			"0".to_string()
		}
		else {
			self.coefficients.iter()
				.enumerate()
				.filter_map(|(i, value)| {
					let suffix = match i {
						0 => "".to_string(),
						1 => "x".to_string(),
						_ => "x^".to_string() + &i.to_string(),
					};
					match value.raw_value {
						0 => None,
						1 if i > 0 => Some(suffix),
						_ => Some(value.to_string() + &suffix),
					}
				})
				.collect::<Vec<String>>()
				.join(" + ")
		};
		write!(f, "{}", formatted)
	}
}


// --- Serialization ---

impl<const N: usize, const Q: u32, const C: u32>
	Serializable
	for Poly<N, Q, C>
{
	fn serialize(&self) -> Vec<bool> {
		let mut result = vec![];
		for value in &self.coefficients {
			result.extend(value.serialize().iter());
		}
		result
	}
	fn deserialize<'a, I>(iter: &mut I) -> Option<Self>
	where
		I: Iterator<Item = &'a bool>
	{
		std::array::try_from_fn(|_| QInt::deserialize(iter))
			.map(|coefficients| Self { coefficients })
	}
}
