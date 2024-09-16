
use crate::math::vector::Vector;
use std::ops::Mul;

pub struct Matrix<const R: usize, const C: usize, const Q: u32> {
	pub rows: [Vector<C, Q>; R],
}
impl<const R: usize, const C: usize, const Q: u32>
	std::fmt::Display
	for Matrix<R, C, Q>
{	
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		for vector in &self.rows {
			writeln!(f, "{}", vector)?;
		}
		Ok(())
	}	
}

impl<const R: usize, const C: usize, const Q: u32>
	Mul<&Vector<C, Q>>
	for &Matrix<R, C, Q>
{
	type Output = Vector<R, Q>;
	
	fn mul(self, rhs: &Vector<C, Q>) -> Self::Output {
		Vector {
			data: std::array::from_fn(|i| &self.rows[i] * rhs),
		}
	}	
}