
use super::ring::{Ring, RingOps};
use crate::util::serializable::Serializable;
use std::ops::{Add, Mul, Sub};

#[derive(Clone, Copy)]
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
}
impl<const Q: u32> Ring for QInt<Q> {
	fn zero() -> Self {
		Self::of_u32(0)
	}
	fn one() -> Self {
		Self::of_u32(1)
	}
}
impl<const Q: u32> RingOps<QInt<Q>> for &QInt<Q> {
	
}
impl<const Q: u32> RingOps<QInt<Q>> for QInt<Q> {
	
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
	fn mul_impl(&self, rhs: &Self) -> Self {
		Self {
			raw_value: (self.raw_value * rhs.raw_value) % Q,
		}
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
