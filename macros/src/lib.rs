
extern crate proc_macro;

use std::iter;
use proc_macro::{Span, TokenStream, TokenTree};
use quote::{quote, quote_spanned};

const N: usize = 256;
const M: usize = 128;
const Q: u32 = 3329;
const ZETA: u32 = 17;
// const N: usize = 4;
// const M: usize = 2;
// const Q: u32 = 5;
// const ZETA: u32 = 2;

fn bit_rev_7(n: u32) -> u32 {
	let mut result = 0;
	let mut source = 1;
	let mut dest = 64;
	while source < 128 {
		if n & source != 0 {
			result |= dest;
		}
		source <<= 1;
		dest >>= 1;
	}
	result
}

fn pow_mod(a: u32, mut b: u32, m: u32) -> u32 {
    let mut result = 1;
    let mut a_pow = a;
    while b > 0 {
        if b % 2 == 1 {
            result = (result * a_pow) % m;
        }
        a_pow = (a_pow * a_pow) % m;
        b /= 2;
    }
    result
}

fn c(i: u32) -> u32 {
    // (Q - pow_mod(ZETA, 2 * bit_rev_7(i as u32) + 1, Q)) % Q
    (Q - pow_mod(ZETA, 2 * i + 1, Q)) % Q
}

#[proc_macro]
pub fn ntt_type(input: TokenStream) -> TokenStream {
    
    if !input.is_empty() {
        return err(Span::call_site(), "expected no arguments");
    }
    
    (0 .. M)
        .map(|i| {
            let c = c(i as u32);
            quote! {
                Poly<2, #Q, #c>
            }
        })
        .rev()
        .fold(
            quote! { QInt<#Q> },
            |acc, poly| quote! {
                DirectSum<#poly, #acc>
            },
        )
        .into()
}

#[proc_macro]
pub fn ntt_impl(input: TokenStream) -> TokenStream {
    
    if !input.is_empty() {
        return err(Span::call_site(), "expected no arguments");
    }
    
    (0 .. M)
        .map(|i| {
            let c = c(i as u32);
            quote! {
                input.rem::<2, #c>()
            }
        })
        .rev()
        .fold(
            quote! { QInt::zero() },
            |acc, poly| quote! {
                DirectSum::new(#poly, #acc)
            },
        )
        .into()
}

#[proc_macro]
pub fn ntt_rev_impl(input: TokenStream) -> TokenStream {
    
    if !input.is_empty() {
        return err(Span::call_site(), "expected no arguments");
    }
    
    let remainder_values = (0 .. M)
        .map(|i| {
            let mut field = quote! { input };
            for _ in 0 .. i {
                field = quote! { #field.b };
            }
            field = quote! { #field.a };
            quote! { #field.embedded() }
        });
    let n_plus_one = N + 1;
    let remainders = quote! {
        let remainders: [Poly<#N, #Q, 1>; #M] = [
            #(#remainder_values),*
        ];
        let original: Poly<#n_plus_one, #Q, 1> = Poly {
            coefficients: std::array::from_fn(|i| match i {
                0 | #N => QInt::one(),
                _ => QInt::zero(),
            }),
        };
    };
    let moduli_values = (0 .. M)
        .map(|i| {
            let c = c(i as u32);
            quote! {
                {
                    let coefficients = std::array::from_fn(|j| match j {
                        0 => QInt::of_u32(#c),
                        2 => QInt::one(),
                        _ => QInt::zero(),
                    });
                    Poly { coefficients }
                }
            }
        });
    let moduli = quote! {
        let moduli: [Poly<#N, #Q, 1>; #M] = [
            #(#moduli_values),*
        ];
    };
    let mapped_values = (0 .. M)
        .map(|i| {
            let c = c(i as u32);
            quote! {
                {
                    let poly = &remainders[#i];
                    let product_of_other_moduli = (&original / moduli[#i].embedded()).rem::<#N, 1>();
                    // let other_product_of_other_moduli = moduli.iter()
                    //     .enumerate()
                    //     .fold(Poly::one(), |acc, (j, modulus)| {
                    //         if j == #i { acc }
                    //         else { acc * modulus }
                    //     });
                    let before = product_of_other_moduli.rem::<2, #c>();
                    let after = before.inv();
                    let inv: Poly<#N, #Q, 1> = after.embedded();
                    poly * product_of_other_moduli * inv
                }
            }
        });
    
    quote! {
        {
            #remainders
            #moduli
            [
                #(#mapped_values),*
            ]
            .iter()
            .fold(Poly::zero(), |acc, p| acc + p)
        }
    }
    .into()
}

#[proc_macro]
pub fn many_greetings(input: TokenStream) -> TokenStream {
	let tokens = input.into_iter().collect::<Vec<_>>();

    // Make sure at least one token is provided.
    if tokens.is_empty() {
        return err(Span::call_site(), "expected integer, found no input");
    }

    // Make sure we don't have too many tokens.
    if tokens.len() > 1 {
        return err(tokens[1].span(), "unexpected second token");
    }

    // Get the number from our token.
    let count = match &tokens[0] {
        TokenTree::Literal(lit) => {
            // Unfortunately, `Literal` doesn't have nice methods right now, so
            // the easiest way for us to get an integer out of it is to convert
            // it into string and parse it again.
            if let Ok(count) = lit.to_string().parse::<usize>() {
                count
            } else {
                let msg = format!("expected unsigned integer, found `{}`", lit);
                return err(lit.span(), msg);
            }
        }
        other => {
            let msg = format!("expected integer literal, found `{}`", other);
            return err(other.span(), msg);
        }
    };

    // Return multiple `println` statements.
    iter::repeat(quote! { println!("Hello"); })
        .map(TokenStream::from)
        .take(count)
        .collect()
}

/// Report an error with the given `span` and message.
fn err(span: Span, msg: impl Into<String>) -> TokenStream {
    let msg = msg.into();
    quote_spanned!(span.into() => {
        compile_error!(#msg);
    }).into()
}
