
use super::ring::{Ring, RingOps};
use crate::util::serializable::Serializable;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct QInt<const Q: u32> {
	pub raw_value: u32,
}
impl<const Q: u32> QInt<Q> {
	pub fn of_u32(raw_value: u32) -> Self {
		Self { raw_value: raw_value % Q }
	}
	pub fn dist(&self, rhs: &QInt<Q>) -> Self {
		let [min, max] = std::cmp::minmax(self.raw_value, rhs.raw_value);
		let dist = std::cmp::min(max - min, min + Q - max);
		Self::of_u32(dist)
	}
	pub fn half() -> Self {
		Self::of_u32(Q / 2)
	}
}
impl<const Q: u32> Ring for QInt<Q> {
	fn zero() -> Self {
		Self::of_u32(0)
	}
	fn one() -> Self {
		Self::of_u32(1)
	}
}
impl<const Q: u32> RingOps<QInt<Q>> for QInt<Q> {}
impl<const Q: u32> RingOps<QInt<Q>> for &QInt<Q> {}

impl<const Q: u32> QInt<Q> {
	fn add_impl(&self, rhs: &Self) -> Self {
		Self {
			raw_value: (self.raw_value + rhs.raw_value) % Q,
		}
	}
	fn sub_impl(&self, rhs: &Self) -> Self {
		Self {
			raw_value: (self.raw_value + Q - rhs.raw_value) % Q,
		}
	}
	fn neg_impl(&self) -> Self {
		Self::zero().sub_impl(self)
	}
	fn mul_impl(&self, rhs: &Self) -> Self {
		Self {
			raw_value: (self.raw_value * rhs.raw_value) % Q,
		}
	}
	fn div_impl(&self, rhs: &Self) -> Self {
		self.mul_impl(&rhs.inv())
	}
	pub fn inv(&self) -> Self {
		assert_ne!(*self, QInt::zero());
		fn gcd(a: u32, b: u32, q: u32) -> (u32, u32, u32) {
			match b {
				0 => (a, 1, 0),
				_ => {
					let (g, x, y) = gcd(b, a % b, q);
					let new_x = y;
					let new_y = (q + x - ((a / b) * y) % q) % q;
					(g, new_x, new_y)
				},
			}
		}
		let (g, x, _y) = gcd(self.raw_value, Q, Q);
		assert_eq!(g, 1);
		Self::of_u32(x)
	}
}

impl<const Q: u32> Add<QInt<Q>> for QInt<Q> {
	type Output = QInt<Q>;
	fn add(self, rhs: QInt<Q>) -> Self::Output {
		self.add_impl(&rhs)
	}
}
impl<const Q: u32> Add<QInt<Q>> for &QInt<Q> {
	type Output = QInt<Q>;
	fn add(self, rhs: QInt<Q>) -> Self::Output {
		self.add_impl(&rhs)
	}
}
impl<const Q: u32> Add<&QInt<Q>> for QInt<Q> {
	type Output = QInt<Q>;
	fn add(self, rhs: &QInt<Q>) -> Self::Output {
		self.add_impl(rhs)
	}
}
impl<const Q: u32> Add<&QInt<Q>> for &QInt<Q> {
	type Output = QInt<Q>;
	fn add(self, rhs: &QInt<Q>) -> Self::Output {
		self.add_impl(rhs)
	}
}
impl<const Q: u32> Sub<QInt<Q>> for QInt<Q> {
	type Output = QInt<Q>;
	fn sub(self, rhs: QInt<Q>) -> Self::Output {
		self.sub_impl(&rhs)
	}
}
impl<const Q: u32> Sub<QInt<Q>> for &QInt<Q> {
	type Output = QInt<Q>;
	fn sub(self, rhs: QInt<Q>) -> Self::Output {
		self.sub_impl(&rhs)
	}
}
impl<const Q: u32> Sub<&QInt<Q>> for QInt<Q> {
	type Output = QInt<Q>;
	fn sub(self, rhs: &QInt<Q>) -> Self::Output {
		self.sub_impl(rhs)
	}
}
impl<const Q: u32> Sub<&QInt<Q>> for &QInt<Q> {
	type Output = QInt<Q>;
	fn sub(self, rhs: &QInt<Q>) -> Self::Output {
		self.sub_impl(rhs)
	}
}
impl<const Q: u32> Neg for QInt<Q> {
	type Output = QInt<Q>;
	fn neg(self) -> Self::Output {
		self.neg_impl()
	}
}
impl<const Q: u32> Neg for &QInt<Q> {
	type Output = QInt<Q>;
	fn neg(self) -> Self::Output {
		self.neg_impl()
	}
}
impl<const Q: u32> Mul<QInt<Q>> for QInt<Q> {
	type Output = QInt<Q>;
	fn mul(self, rhs: QInt<Q>) -> Self::Output {
		self.mul_impl(&rhs)
	}
}
impl<const Q: u32> Mul<QInt<Q>> for &QInt<Q> {
	type Output = QInt<Q>;
	fn mul(self, rhs: QInt<Q>) -> Self::Output {
		self.mul_impl(&rhs)
	}
}
impl<const Q: u32> Mul<&QInt<Q>> for QInt<Q> {
	type Output = QInt<Q>;
	fn mul(self, rhs: &QInt<Q>) -> Self::Output {
		self.mul_impl(rhs)
	}
}
impl<const Q: u32> Mul<&QInt<Q>> for &QInt<Q> {
	type Output = QInt<Q>;
	fn mul(self, rhs: &QInt<Q>) -> Self::Output {
		self.mul_impl(rhs)
	}
}
impl<const Q: u32> Div<QInt<Q>> for QInt<Q> {
	type Output = QInt<Q>;
	fn div(self, rhs: QInt<Q>) -> Self::Output {
		self.div_impl(&rhs)
	}
}
impl<const Q: u32> Div<QInt<Q>> for &QInt<Q> {
	type Output = QInt<Q>;
	fn div(self, rhs: QInt<Q>) -> Self::Output {
		self.div_impl(&rhs)
	}
}
impl<const Q: u32> Div<&QInt<Q>> for QInt<Q> {
	type Output = QInt<Q>;
	fn div(self, rhs: &QInt<Q>) -> Self::Output {
		self.div_impl(rhs)
	}
}
impl<const Q: u32> Div<&QInt<Q>> for &QInt<Q> {
	type Output = QInt<Q>;
	fn div(self, rhs: &QInt<Q>) -> Self::Output {
		self.div_impl(rhs)
	}
}


// --- Assignment Operators ---

impl<const Q: u32> AddAssign<&QInt<Q>> for QInt<Q> {
	fn add_assign(&mut self, rhs: &QInt<Q>) {
		*self = *self + rhs
	}
}
impl<const Q: u32> AddAssign<QInt<Q>> for QInt<Q> {
	fn add_assign(&mut self, rhs: QInt<Q>) {
		*self = *self + rhs
	}
}
impl<const Q: u32> SubAssign<&QInt<Q>> for QInt<Q> {
	fn sub_assign(&mut self, rhs: &QInt<Q>) {
		*self = *self - rhs
	}
}
impl<const Q: u32> SubAssign<QInt<Q>> for QInt<Q> {
	fn sub_assign(&mut self, rhs: QInt<Q>) {
		*self = *self - rhs
	}
}
impl<const Q: u32> MulAssign<&QInt<Q>> for QInt<Q> {
	fn mul_assign(&mut self, rhs: &QInt<Q>) {
		*self = *self * rhs
	}
}
impl<const Q: u32> MulAssign<QInt<Q>> for QInt<Q> {
	fn mul_assign(&mut self, rhs: QInt<Q>) {
		*self = *self * rhs
	}
}
impl<const Q: u32> DivAssign<&QInt<Q>> for QInt<Q> {
	fn div_assign(&mut self, rhs: &QInt<Q>) {
		*self = *self / rhs
	}
}
impl<const Q: u32> DivAssign<QInt<Q>> for QInt<Q> {
	fn div_assign(&mut self, rhs: QInt<Q>) {
		*self = *self / rhs
	}
}


// --- Serialization ---

impl<const Q: u32> Serializable for QInt<Q> {
	fn serialize(&self) -> Vec<bool> {
		let mut q = Q;
		let mut value = self.raw_value;
		let mut result = vec![];
		while q > 0 {
			result.push(value % 2 == 1);
			value /= 2;
			q /= 2;
		}
		result
	}
	fn deserialize<'a, I>(iter: &mut I) -> Option<Self>
	where
		I: Iterator<Item = &'a bool>
	{
		let mut q = 1;
		let mut value = 0;
		while q < Q {
			match iter.next() {
				None => return None,
				Some(&bit) => {
					if bit {
						value += q;
					}
				}
			};
			q *= 2;
		}
		Some(Self::of_u32(value))
	}
}


// --- Displaying ---

impl<const Q: u32> std::fmt::Display for QInt<Q> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.raw_value)
	}
}


pub fn rem_nonneg<const Q: u32>(value: i32) -> u32 {
	let q_i = Q as i32;
	let rem = value % q_i;
	if rem < 0 {
		return (rem + q_i) as u32;
	}
	else {
		return rem as u32;
	}
}
