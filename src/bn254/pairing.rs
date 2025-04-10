use super::*;

use ark_bn254::{Bn254, Fq, Fq12, Fq2, Fq6};
use ark_ec::bn::{G1Prepared, G2Prepared};
use ark_ec::pairing::{MillerLoopOutput, Pairing, PairingOutput};
use ark_ff::{AdditiveGroup, Field, PrimeField};
use ark_serialize::Valid;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use zeroize::DefaultIsZeroes;

pub fn multi_miller_loop(terms: &[(&G1Affine, &G2Affine)]) -> MillerLoopResult {
    let g1_terms = terms.into_iter().map(|(&g1, _)| G1Prepared::from(g1.0));
    let g2_terms = terms.into_iter().map(|(_, &g2)| G2Prepared::from(g2.0));
    MillerLoopResult(Bn254::multi_miller_loop(g1_terms, g2_terms))
}

#[derive(Copy, Clone, Debug)]
pub struct MillerLoopResult(pub(crate) MillerLoopOutput<Bn254>);

impl MillerLoopResult {
    pub fn final_exponentiation(&self) -> Gt {
        let res = Bn254::final_exponentiation(self.0).unwrap();
        Gt(res)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Gt(pub(crate) PairingOutput<Bn254>);

impl Default for Gt {
    fn default() -> Self {
        Self(PairingOutput::default())
    }
}

impl DefaultIsZeroes for Gt {}

impl ConstantTimeEq for Gt {
    fn ct_eq(&self, other: &Self) -> Choice {
        fq12_constant_time_eq(&self.0 .0, &other.0 .0)
    }
}

impl Eq for Gt {}

impl PartialEq for Gt {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl Gt {
    pub const ZERO: Self = Self(PairingOutput::ZERO);
}

fn fq6_conditionally_selectable(a: &Fq6, b: &Fq6, choice: Choice) -> Fq6 {
    Fq6::new(
        G2Projective::fq2_conditional_select(&a.c0, &b.c0, choice),
        G2Projective::fq2_conditional_select(&a.c1, &b.c1, choice),
        G2Projective::fq2_conditional_select(&a.c2, &b.c2, choice),
    )
}

fn fq12_constant_time_eq(a: &Fq12, b: &Fq12) -> Choice {
    let c0 = fq6_constant_time_eq(&a.c0, &b.c0);
    let c1 = fq6_constant_time_eq(&a.c1, &b.c1);
    c0 & c1
}

fn fq6_constant_time_eq(a: &Fq6, b: &Fq6) -> Choice {
    let c0 = fq2_constant_time_eq(&a.c0, &b.c0);
    let c1 = fq2_constant_time_eq(&a.c1, &b.c1);
    let c2 = fq2_constant_time_eq(&a.c2, &b.c2);
    c0 & c1 & c2
}

fn fq2_constant_time_eq(a: &Fq2, b: &Fq2) -> Choice {
    let c0 = fq_constant_time_eq(&a.c0, &b.c0);
    let c1 = fq_constant_time_eq(&a.c1, &b.c1);
    c0 & c1
}

fn fq_constant_time_eq(a: &Fq, b: &Fq) -> Choice {
    let lhs = a.into_bigint().0;
    let rhs = b.into_bigint().0;

    let mut res = Choice::from(1u8);
    for i in 0..4 {
        res &= lhs[i].ct_eq(&rhs[i]);
    }
    res
}
