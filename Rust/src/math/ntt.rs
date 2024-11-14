
use crate::math::direct_sum::DirectSum;
use crate::math::poly::Poly;
use crate::math::qint::QInt;
use crate::math::ring::Ring;
use crate::math::vector::Vector;
use kyber_macros::{ntt_impl, ntt_rev_impl, ntt_type};

use super::matrix::Matrix;

const N: usize = 256;
const Q: u32 = 3329;

pub type NTT = ntt_type!();

fn ntt_convert(input: &Poly<N, Q, 1>) -> NTT {
	ntt_impl!()
}
fn ntt_inv_convert(input: &NTT) -> Poly<N, Q, 1> {
	ntt_rev_impl!()
}

impl NTT {
	pub fn convert_poly(poly: &Poly<N, Q, 1>) -> Self {
		ntt_convert(poly)
	}
	pub fn convert_poly_vector<const M: usize>(vec: &Vector<Poly<N, Q, 1>, M>) -> Vector<Self, M> {
		Vector {
			data: vec.data.clone().map(|poly| Self::convert_poly(&poly)),
		}
	}
	pub fn convert_poly_matrix<const R: usize, const C: usize>(matrix: &Matrix<Poly<N, Q, 1>, R, C>) -> Matrix<Self, R, C> {
		Matrix {
			rows: matrix.rows.clone().map(|row| Self::convert_poly_vector(&row)),
		}
	}
	pub fn inv_convert_poly(ntt: &Self) -> Poly<N, Q, 1> {
		ntt_inv_convert(ntt)
	}
	pub fn inv_convert_poly_vector<const M: usize>(vec: &Vector<Self, M>) -> Vector<Poly<N, Q, 1>, M> {
		Vector {
			data: vec.data.clone().map(|ntt| Self::inv_convert_poly(&ntt)),
		}
	}
}
