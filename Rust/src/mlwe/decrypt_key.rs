
use crate::math::{ntt::NTT, vector::Vector};

pub struct DecryptKey<const N: usize, const R: usize, const Q: u32> {
	pub s: Vector<NTT, R>,
}
