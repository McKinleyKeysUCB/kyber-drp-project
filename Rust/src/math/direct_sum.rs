
use super::{qint::QInt, ring::{Ring, RingOps}};
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


// --- Scalar Multiplication ---

impl<A, B, X, Y, const Q: u32>
	Mul<QInt<Q>>
	for DirectSum<A, B>
	where
		A: Ring + for<'a> Mul<&'a QInt<Q>, Output = X>,
		for<'a> &'a A: RingOps<A>,
		B: Ring + for<'a> Mul<&'a QInt<Q>, Output = Y>,
		for<'a> &'a B: RingOps<B>,
{
	type Output = DirectSum<X, Y>;
	fn mul(self, rhs: QInt<Q>) -> Self::Output {
		Self::Output {
			a: self.a * &rhs,
			b: self.b * &rhs,
		}
	}
}
impl<A, B, X, Y, const Q: u32>
	Mul<QInt<Q>>
	for &DirectSum<A, B>
	where
		A: Ring,
		for<'a, 'b> &'a A: RingOps<A> + Mul<&'a QInt<Q>, Output = X>,
		B: Ring,
		for<'a, 'b> &'a B: RingOps<B> + Mul<&'a QInt<Q>, Output = Y>,
{
	type Output = DirectSum<X, Y>;
	fn mul(self, rhs: QInt<Q>) -> Self::Output {
		Self::Output {
			a: &self.a * &rhs,
			b: &self.b * &rhs,
		}
	}
}
impl<A, B, X, Y, const Q: u32>
	Mul<&QInt<Q>>
	for DirectSum<A, B>
	where
		A: Ring + for<'a> Mul<&'a QInt<Q>, Output = X>,
		for<'a> &'a A: RingOps<A>,
		B: Ring + for<'a> Mul<&'a QInt<Q>, Output = Y>,
		for<'a> &'a B: RingOps<B>,
{
	type Output = DirectSum<X, Y>;
	fn mul(self, rhs: &QInt<Q>) -> Self::Output {
		Self::Output {
			a: self.a * rhs,
			b: self.b * rhs,
		}
	}
}
impl<A, B, X, Y, const Q: u32>
	Mul<&QInt<Q>>
	for &DirectSum<A, B>
	where
		A: Ring,
		for<'a, 'b> &'a A: RingOps<A> + Mul<&'a QInt<Q>, Output = X>,
		B: Ring,
		for<'a, 'b> &'a B: RingOps<B> + Mul<&'a QInt<Q>, Output = Y>,
{
	type Output = DirectSum<X, Y>;
	fn mul(self, rhs: &QInt<Q>) -> Self::Output {
		Self::Output {
			a: &self.a * rhs,
			b: &self.b * rhs,
		}
	}
}

// impl<A, B, X, Y, const Q: u32>
// 	Mul<DirectSum<A, B>>
// 	for QInt<Q>
// 	where
// 		A: Ring,
// 		for<'a> &'a A: RingOps<A>,
// 		B: Ring,
// 		for<'a> &'a B: RingOps<B>,
// 		for<'q> &'q QInt<Q>: Mul<A, Output = X> + Mul<B, Output = Y>,
// {
// 	type Output = DirectSum<X, Y>;
// 	fn mul(self, rhs: DirectSum<A, B>) -> Self::Output {
// 		Self::Output {
// 			a: &self * rhs.a,
// 			b: &self * rhs.b,
// 		}
// 	}
// }
// impl<A, B, X, Y, const Q: u32>
// 	Mul<&DirectSum<A, B>>
// 	for QInt<Q>
// 	where
// 		A: Ring,
// 		for<'a> &'a A: RingOps<A>,
// 		B: Ring,
// 		for<'a> &'a B: RingOps<B>,
// 		for<'q, 'a, 'b> &'q QInt<Q>: Mul<&'a A, Output = X> + Mul<&'b B, Output = Y>,
// {
// 	type Output = DirectSum<X, Y>;
// 	fn mul(self, rhs: &DirectSum<A, B>) -> Self::Output {
// 		Self::Output {
// 			a: &self * &rhs.a,
// 			b: &self * &rhs.b,
// 		}
// 	}
// }
// impl<A, B, X, Y, const Q: u32>
// 	Mul<DirectSum<A, B>>
// 	for &QInt<Q>
// 	where
// 		A: Ring,
// 		for<'a> &'a A: RingOps<A>,
// 		B: Ring,
// 		for<'a> &'a B: RingOps<B>,
// 		for<'q> &'q QInt<Q>: Mul<A, Output = X> + Mul<B, Output = Y>,
// {
// 	type Output = DirectSum<X, Y>;
// 	fn mul(self, rhs: DirectSum<A, B>) -> Self::Output {
// 		Self::Output {
// 			a: self * rhs.a,
// 			b: self * rhs.b,
// 		}
// 	}
// }
// impl<A, B, X, Y, const Q: u32>
// 	Mul<&DirectSum<A, B>>
// 	for &QInt<Q>
// 	where
// 		A: Ring,
// 		for<'a> &'a A: RingOps<A>,
// 		B: Ring,
// 		for<'a> &'a B: RingOps<B>,
// 		for<'q, 'a, 'b> &'q QInt<Q>: Mul<&'a A, Output = X> + Mul<&'b B, Output = Y>,
// {
// 	type Output = DirectSum<X, Y>;
// 	fn mul(self, rhs: &DirectSum<A, B>) -> Self::Output {
// 		Self::Output {
// 			a: self * &rhs.a,
// 			b: self * &rhs.b,
// 		}
// 	}
// }


// impl<const N: usize, const C: u32, B, Y, const Q: u32>
// 	Mul<DirectSum<Poly<N, Q, C>, B>>
// 	for QInt<Q>
// 	where
// 		B: Ring,
// 		for<'a> &'a B: RingOps<B>,
// 		for<'q> &'q QInt<Q>: Mul<B, Output = Y>,
// {
// 	type Output = DirectSum<Poly<N, Q, C>, Y>;
// 	fn mul(self, rhs: DirectSum<Poly<N, Q, C>, B>) -> Self::Output {
// 		Self::Output {
// 			a: &self * rhs.a,
// 			b: &self * rhs.b,
// 		}
// 	}
// }
// impl<A, B, X, Y, const Q: u32>
// 	Mul<&DirectSum<A, B>>
// 	for QInt<Q>
// 	where
// 		A: Ring,
// 		for<'a> &'a A: RingOps<A>,
// 		B: Ring,
// 		for<'a> &'a B: RingOps<B>,
// 		for<'q, 'a, 'b> &'q QInt<Q>: Mul<&'a A, Output = X> + Mul<&'b B, Output = Y>,
// {
// 	type Output = DirectSum<X, Y>;
// 	fn mul(self, rhs: &DirectSum<A, B>) -> Self::Output {
// 		Self::Output {
// 			a: &self * &rhs.a,
// 			b: &self * &rhs.b,
// 		}
// 	}
// }
// impl<A, B, X, Y, const Q: u32>
// 	Mul<DirectSum<A, B>>
// 	for &QInt<Q>
// 	where
// 		A: Ring,
// 		for<'a> &'a A: RingOps<A>,
// 		B: Ring,
// 		for<'a> &'a B: RingOps<B>,
// 		for<'q> &'q QInt<Q>: Mul<A, Output = X> + Mul<B, Output = Y>,
// {
// 	type Output = DirectSum<X, Y>;
// 	fn mul(self, rhs: DirectSum<A, B>) -> Self::Output {
// 		Self::Output {
// 			a: self * rhs.a,
// 			b: self * rhs.b,
// 		}
// 	}
// }
// impl<const N: usize, const C: u32, B, const Q: u32>
// 	Mul<&DirectSum<Poly<N, Q, C>, B>>
// 	for &QInt<Q>
// 	where
// 		B: Ring,
// 		for<'a> &'a B: RingOps<B>,
// 		for<'q, 'b> &'q QInt<Q>: Mul<&'b B, Output = B>,
// {
// 	type Output = DirectSum<Poly<N, Q, C>, B>;
// 	fn mul(self, rhs: &DirectSum<Poly<N, Q, C>, B>) -> Self::Output {
// 		Self::Output {
// 			a: self * &rhs.a,
// 			b: self * &rhs.b,
// 		}
// 	}
// }



// impl<A, B, X, Y, T>
// 	Mul<T>
// 	for DirectSum<A, B>
// 	where
// 		T: Drop,
// 		A: Ring + for<'a> Mul<&'a T, Output = X>,
// 		for<'a> &'a A: RingOps<A>,
// 		B: Ring + for<'a> Mul<&'a T, Output = Y>,
// 		for<'a> &'a B: RingOps<B>,
// {
// 	type Output = DirectSum<X, Y>;
// 	fn mul(self, rhs: T) -> Self::Output {
// 		Self::Output {
// 			a: self.a * &rhs,
// 			b: self.b * &rhs,
// 		}
// 	}
// }
// impl<A, B, X, Y, T>
// 	Mul<T>
// 	for &DirectSum<A, B>
// 	where
// 		T: Clone,
// 		A: Ring,
// 		for<'a> &'a A: RingOps<A> + Mul<T, Output = X>,
// 		B: Ring,
// 		for<'a> &'a B: RingOps<B> + Mul<T, Output = Y>,
// {
// 	type Output = DirectSum<X, Y>;
// 	fn mul(self, rhs: T) -> Self::Output {
// 		Self::Output {
// 			a: &self.a * rhs.clone(),
// 			b: &self.b * rhs,
// 		}
// 	}
// }
// impl<A, B, X, Y, T>
// 	Mul<T>
// 	for DirectSum<A, B>
// 	where
// 		T: Clone,
// 		A: Ring + Mul<T, Output = X>,
// 		for<'a> &'a A: RingOps<A>,
// 		B: Ring + Mul<T, Output = Y>,
// 		for<'a> &'a B: RingOps<B>,
// {
// 	type Output = DirectSum<X, Y>;
// 	fn mul(self, rhs: T) -> Self::Output {
// 		Self::Output {
// 			a: self.a * rhs.clone(),
// 			b: self.b * rhs,
// 		}
// 	}
// }
// impl<A, B, X, Y, T>
// 	Mul<T>
// 	for &DirectSum<A, B>
// 	where
// 		T: Clone,
// 		A: Ring,
// 		for<'a> &'a A: RingOps<A> + Mul<T, Output = X>,
// 		B: Ring,
// 		for<'a> &'a B: RingOps<B> + Mul<T, Output = Y>,
// {
// 	type Output = DirectSum<X, Y>;
// 	fn mul(self, rhs: T) -> Self::Output {
// 		Self::Output {
// 			a: &self.a * rhs.clone(),
// 			b: &self.b * rhs,
// 		}
// 	}
// }


// impl<A, B, X, Y, T>
// 	Mul<&T>
// 	for DirectSum<A, B>
// 	where
// 		A: Ring + for<'a> Mul<&'a T, Output = X>,
// 		for<'a> &'a A: RingOps<A>,
// 		B: Ring + for<'a> Mul<&'a T, Output = Y>,
// 		for<'a> &'a B: RingOps<B>,
// {
// 	type Output = DirectSum<X, Y>;
// 	fn mul(self, rhs: &T) -> Self::Output {
// 		Self::Output {
// 			a: self.a * rhs,
// 			b: self.b * rhs,
// 		}
// 	}
// }
// impl<A, B, X, Y, T>
// 	Mul<T>
// 	for &DirectSum<A, B>
// 	where
// 		A: Ring,
// 		for<'a, 'b> &'a A: RingOps<A> + Mul<&'b T, Output = X>,
// 		B: Ring,
// 		for<'a, 'b> &'a B: RingOps<B> + Mul<&'b T, Output = Y>,
// {
// 	type Output = DirectSum<X, Y>;
// 	fn mul(self, rhs: T) -> Self::Output {
// 		Self::Output {
// 			a: &self.a * &rhs,
// 			b: &self.b * &rhs,
// 		}
// 	}
// }
