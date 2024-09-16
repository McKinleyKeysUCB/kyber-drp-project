
use std::ops::Add;
use std::ops::Mul;

#[derive(Clone, Copy)]
pub struct QUInt<const Q: u32> {
	pub raw_value: u32,
}
impl<const Q: u32> QUInt<Q> {
	pub fn of_u32(raw_value: u32) -> Self {
		Self { raw_value: raw_value % Q }
	}
	pub fn zero() -> Self {
		Self::of_u32(0)
	}
	pub fn dist(&self, rhs: &QUInt<Q>) -> Self {
		let [min, max] = std::cmp::minmax(self.raw_value, rhs.raw_value);
		let dist = std::cmp::min(max - min, min + Q - max);
		Self::of_u32(dist)
	}
	pub fn serialize(&self) -> Vec<bool> {
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
	pub fn deserialize(bits: &Vec<bool>) -> Self {
		let mut q = 1;
		let mut value = 0;
		let mut i = 0;
		while q < Q {
			if bits[i] {
				value += q;
			}
			q *= 2;
			i += 1;
		}
		// TODO: Return Result
		Self::of_u32(value)
	}
}
impl<const Q: u32> std::fmt::Display for QUInt<Q> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.raw_value)
	}
}

pub struct QInt<const Q: u32> {
	raw_value: i32,
}
impl<const Q: u32> QInt<Q> {
	pub fn of_i32(raw_value: i32) -> Self {
		Self { raw_value: raw_value % (Q as i32) }
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

impl<const Q: u32> Add<QUInt<Q>> for QUInt<Q> {
	type Output = QUInt<Q>;
	fn add(self, rhs: QUInt<Q>) -> Self::Output {
		Self::Output {
			raw_value: (self.raw_value + rhs.raw_value) % Q,
		}
	}
}
impl<const Q: u32> Add<QInt<Q>> for QUInt<Q> {
	type Output = QUInt<Q>;
	fn add(self, rhs: QInt<Q>) -> Self::Output {
		Self::Output {
			raw_value: rem_nonneg::<Q>(self.raw_value as i32 + rhs.raw_value),
		}
	}
}
impl<const Q: u32> Mul<QUInt<Q>> for QUInt<Q> {
	type Output = QUInt<Q>;
	fn mul(self, rhs: QUInt<Q>) -> Self::Output {
		Self::Output {
			raw_value: (self.raw_value * rhs.raw_value) % Q,
		}
	}
}