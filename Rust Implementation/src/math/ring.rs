
use std::ops::{Add, Div, Mul, Sub};

pub trait RingOps<Base>:
	Add<Base, Output = Base> +
	Sub<Base, Output = Base> +
	Mul<Base, Output = Base> +
	Div<Base, Output = Base> +
	for<'a> Add<&'a Base, Output = Base> +
	for<'a> Sub<&'a Base, Output = Base> +
	for<'a> Mul<&'a Base, Output = Base> +
	for<'a> Div<&'a Base, Output = Base> +
	Sized
{}

pub trait Ring:
	RingOps<Self>
	where for<'a> &'a Self: RingOps<Self>
{
    fn zero() -> Self;
    fn one() -> Self;
}
