
pub struct Bits<const N: usize> {
	pub data: [bool; N],
}
impl<const N: usize>
	std::fmt::Display
	for Bits<N>
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.data.iter().rev().map(|&b| if b { '1' } else { '0' }).collect::<String>())
	}
}
