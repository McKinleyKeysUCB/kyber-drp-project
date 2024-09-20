
use crate::math::{ring::{Ring, RingOps}, vector::Vector};
use std::ops::Mul;

pub struct Matrix<T, const R: usize, const C: usize> where T: Ring, for<'a> &'a T: RingOps<T> {
	pub rows: [Vector<T, C>; R],
}
impl<T, const R: usize, const C: usize>
	std::fmt::Display
	for Matrix<T, R, C>
	where T: std::fmt::Display + Ring, for<'a> &'a T: RingOps<T>
{	
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		for vector in &self.rows {
			writeln!(f, "{}", vector)?;
		}
		Ok(())
	}
}

impl<T, const R: usize, const C: usize>
	Mul<&Vector<T, C>>
	for &Matrix<T, R, C>
	where T: Ring, for<'a> &'a T: RingOps<T>
{
	type Output = Vector<T, R>;
	fn mul(self, rhs: &Vector<T, C>) -> Self::Output {
		Vector {
			data: std::array::from_fn(|i| &self.rows[i] * rhs),
		}
	}
}