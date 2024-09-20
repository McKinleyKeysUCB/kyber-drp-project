
use super::qint::QInt;

/// A member of `Z_Q[x]/(x^N + 1)`.
pub struct Poly<const N: usize, const Q: u32> {
	pub coefficients: [QInt<Q>; N],
}

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

impl<const N: usize, const Q: u32>
	std::ops::Add<&Poly<N, Q>>
	for &Poly<N, Q>
{
	type Output = Poly<N, Q>;
	fn add(self, rhs: &Poly<N, Q>) -> Self::Output {
		let coefficients = std::array::from_fn(|i| self.coefficients[i] + rhs.coefficients[i]);
		Self::Output { coefficients }
	}
}
impl<const N: usize, const Q: u32>
	std::ops::Mul<&Poly<N, Q>>
	for &Poly<N, Q>
{
	type Output = Poly<N, Q>;
	fn mul(self, rhs: &Poly<N, Q>) -> Self::Output {
		let coefficients = std::array::from_fn(|i| {
			let positive = (0 ..= i).fold(QInt::zero(), |acc, j| {
				acc + self.coefficients[j] * rhs.coefficients[i - j]
			});
			let negative = (i + 1 .. N).fold(QInt::zero(), |acc, j| {
				acc + self.coefficients[j] * rhs.coefficients[i + N - j]
			});
			positive - negative
		});
		Self::Output { coefficients }
	}
}
