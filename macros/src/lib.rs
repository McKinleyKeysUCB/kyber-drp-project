
extern crate proc_macro;

use std::iter;
use proc_macro::{Span, TokenStream, TokenTree};
use quote::{quote, quote_spanned};

const Q: u32 = 3329;
const ZETA: u32 = 17;

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
        a_pow = (a_pow * a) % m;
        b /= 2;
    }
    result
}

fn c(i: u32) -> u32 {
    Q - pow_mod(ZETA, 2 * bit_rev_7(i as u32) + 1, Q)
}

#[proc_macro]
pub fn ntt_type(input: TokenStream) -> TokenStream {
    
    if !input.is_empty() {
        return err(Span::call_site(), "expected no arguments");
    }
    
    (0 .. 128)
        .map(|i| {
            let c = c(i);
            quote! {
                Poly<2, #Q, #c>
            }
        })
        .rev()
        .reduce(|acc, poly| quote! {
            DirectSum<#poly, #acc>
        })
        .unwrap()
        .into()
}

#[proc_macro]
pub fn ntt_impl(input: TokenStream) -> TokenStream {
    
    if !input.is_empty() {
        return err(Span::call_site(), "expected no arguments");
    }
    
    (0 .. 128)
        .map(|i| {
            let c = c(i);
            quote! {
                input.rem::<2, #c>()
            }
        })
        .rev()
        .reduce(|acc, poly| quote! {
            DirectSum::new(#poly, #acc)
        })
        .unwrap()
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
