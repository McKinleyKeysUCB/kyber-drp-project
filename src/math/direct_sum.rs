
use super::ring::{Ring, RingOps};
use std::ops::{Add, Div, Mul, Sub};

#[derive(Clone, Debug)]
pub struct DirectSum<A, B> {
    pub a: A,
    pub b: B,
}
impl<A, B> DirectSum<A, B> {
	pub fn new(a: A, b: B) -> Self {
		Self { a, b }
	}
}

impl<A, B>
	Ring
	for DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    fn zero() -> Self {
        Self {
            a: A::zero(),
            b: B::zero(),
        }
    }
    fn one() -> Self {
        Self {
            a: A::one(),
            b: B::one(),
        }
    }
}
impl<A, B>
	RingOps<DirectSum<A, B>>
	for DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{}
impl<A, B>
	RingOps<DirectSum<A, B>>
	for &DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{}

impl<A, B>
	DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    fn add_impl(&self, rhs: &Self) -> Self {
		Self {
			a: &self.a + &rhs.a,
			b: &self.b + &rhs.b,
		}
    }
    fn sub_impl(&self, rhs: &Self) -> Self {
        Self {
			a: &self.a - &rhs.a,
			b: &self.b - &rhs.b,
		}
    }
    fn mul_impl(&self, rhs: &Self) -> Self {
        Self {
			a: &self.a * &rhs.a,
			b: &self.b * &rhs.b,
		}
    }
	fn div_impl(&self, rhs: &Self) -> Self {
        Self {
			a: &self.a / &rhs.a,
			b: &self.b / &rhs.b,
		}
    }
}

impl<A, B>
	Add<DirectSum<A, B>>
	for DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    type Output = DirectSum<A, B>;
    fn add(self, rhs: DirectSum<A, B>) -> Self::Output {
        self.add_impl(&rhs)
    }
}
impl<A, B>
	Add<DirectSum<A, B>>
	for &DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    type Output = DirectSum<A, B>;
    fn add(self, rhs: DirectSum<A, B>) -> Self::Output {
        self.add_impl(&rhs)
    }
}
impl<A, B>
	Add<&DirectSum<A, B>>
	for DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    type Output = DirectSum<A, B>;
    fn add(self, rhs: &DirectSum<A, B>) -> Self::Output {
        self.add_impl(rhs)
    }
}
impl<A, B>
	Add<&DirectSum<A, B>>
	for &DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    type Output = DirectSum<A, B>;
    fn add(self, rhs: &DirectSum<A, B>) -> Self::Output {
        self.add_impl(rhs)
    }
}
impl<A, B>
	Sub<DirectSum<A, B>>
	for DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    type Output = DirectSum<A, B>;
    fn sub(self, rhs: DirectSum<A, B>) -> Self::Output {
        self.sub_impl(&rhs)
    }
}
impl<A, B>
	Sub<DirectSum<A, B>>
	for &DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    type Output = DirectSum<A, B>;
    fn sub(self, rhs: DirectSum<A, B>) -> Self::Output {
        self.sub_impl(&rhs)
    }
}
impl<A, B>
	Sub<&DirectSum<A, B>>
	for DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    type Output = DirectSum<A, B>;
    fn sub(self, rhs: &DirectSum<A, B>) -> Self::Output {
        self.sub_impl(rhs)
    }
}
impl<A, B>
	Sub<&DirectSum<A, B>>
	for &DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    type Output = DirectSum<A, B>;
    fn sub(self, rhs: &DirectSum<A, B>) -> Self::Output {
        self.sub_impl(rhs)
    }
}
impl<A, B>
	Mul<DirectSum<A, B>>
	for DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    type Output = DirectSum<A, B>;
    fn mul(self, rhs: DirectSum<A, B>) -> Self::Output {
        self.mul_impl(&rhs)
    }
}
impl<A, B>
	Mul<DirectSum<A, B>>
	for &DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    type Output = DirectSum<A, B>;
    fn mul(self, rhs: DirectSum<A, B>) -> Self::Output {
        self.mul_impl(&rhs)
    }
}
impl<A, B>
	Mul<&DirectSum<A, B>>
	for DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    type Output = DirectSum<A, B>;
    fn mul(self, rhs: &DirectSum<A, B>) -> Self::Output {
        self.mul_impl(rhs)
    }
}
impl<A, B>
	Mul<&DirectSum<A, B>>
	for &DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    type Output = DirectSum<A, B>;
    fn mul(self, rhs: &DirectSum<A, B>) -> Self::Output {
        self.mul_impl(rhs)
    }
}
impl<A, B>
	Div<DirectSum<A, B>>
	for DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    type Output = DirectSum<A, B>;
    fn div(self, rhs: DirectSum<A, B>) -> Self::Output {
        self.div_impl(&rhs)
    }
}
impl<A, B>
	Div<DirectSum<A, B>>
	for &DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    type Output = DirectSum<A, B>;
    fn div(self, rhs: DirectSum<A, B>) -> Self::Output {
        self.div_impl(&rhs)
    }
}
impl<A, B>
	Div<&DirectSum<A, B>>
	for DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    type Output = DirectSum<A, B>;
    fn div(self, rhs: &DirectSum<A, B>) -> Self::Output {
        self.div_impl(rhs)
    }
}
impl<A, B>
	Div<&DirectSum<A, B>>
	for &DirectSum<A, B>
	where
		A: Ring,
		for<'a> &'a A: RingOps<A>,
		B: Ring,
		for<'a> &'a B: RingOps<B>,
{
    type Output = DirectSum<A, B>;
    fn div(self, rhs: &DirectSum<A, B>) -> Self::Output {
        self.div_impl(rhs)
    }
}
