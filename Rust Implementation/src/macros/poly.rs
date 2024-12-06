
#[macro_export]
macro_rules! len {
    () => { 0 };
    ($head:expr $(, $tail:expr)* $(,)?) => { 1 + $crate::len!($($tail),*) };
}

#[macro_export]
macro_rules! poly {
    (<Q = $q:literal> [$($x:expr),* $(,)?]) => {
        poly!(<Q = {$q}>[$($x),*])
    };
    (<Q = {$q:expr}> [$($x:expr),* $(,)?]) => {
        {
            const N: usize = $crate::len!($($x),*);
            $crate::math::poly::Poly::<N, $q, 1> { coefficients: [$(QInt::of_u32($x)),+] }
        }
    };
    ($($x:expr),* $(,)?) => {
        poly!(<Q = {Q}>[$($x),*])
    };
}
