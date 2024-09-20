
pub trait Serializable
	where Self: Sized
{
	fn serialize(&self) -> Vec<bool>;
	fn deserialize<'a, I>(iter: &mut I) -> Option<Self>
		where I: Iterator<Item = &'a bool>;
}
