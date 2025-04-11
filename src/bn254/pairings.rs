use super::*;
use std::borrow::Borrow;
use std::iter::Sum;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use ark_bn254::{Bn254 as ArkBn254, Fq, Fq12, Fq2, Fq6};
use ark_ec::bn::{G1Prepared, G2Prepared as Bn254G2Prepared};
use ark_ec::pairing::{MillerLoopOutput, Pairing, PairingOutput};
use ark_ff::{AdditiveGroup, FftField, PrimeField, Zero};
use ark_std::UniformRand;
use elliptic_curve::Group;
use pairing::{Engine, MultiMillerLoop, PairingCurveAffine};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use zeroize::DefaultIsZeroes;

#[derive(Copy, Clone, Debug)]
pub struct Bn254;

impl Engine for Bn254 {
    type Fr = Scalar;
    type G1 = G1Projective;
    type G1Affine = G1Affine;
    type G2 = G2Projective;
    type G2Affine = G2Affine;
    type Gt = Gt;

    fn pairing(p: &Self::G1Affine, q: &Self::G2Affine) -> Self::Gt {
        Gt(ArkBn254::pairing(
            G1Prepared::from(p.0),
            Bn254G2Prepared::from(q.0),
        ))
    }
}

impl MultiMillerLoop for Bn254 {
    type G2Prepared = G2Prepared;
    type Result = MillerLoopResult;

    fn multi_miller_loop(terms: &[(&Self::G1Affine, &Self::G2Prepared)]) -> Self::Result {
        multi_miller_loop(terms)
    }
}

pub fn multi_miller_loop(terms: &[(&G1Affine, &G2Prepared)]) -> MillerLoopResult {
    let g1_terms = terms.iter().map(|(&g1, _)| G1Prepared::from(g1.0));
    let g2_terms = terms.iter().map(|(_, g2)| Bn254G2Prepared {
        ell_coeffs: g2.0.ell_coeffs.clone(),
        infinity: g2.0.infinity,
    });
    MillerLoopResult(ArkBn254::multi_miller_loop(g1_terms, g2_terms))
}

pub struct G2Prepared(pub(crate) Bn254G2Prepared<ark_bn254::Config>);

impl Clone for G2Prepared {
    fn clone(&self) -> Self {
        Self(Bn254G2Prepared {
            ell_coeffs: self.0.ell_coeffs.clone(),
            infinity: self.0.infinity,
        })
    }
}

impl From<G2Affine> for G2Prepared {
    fn from(g2: G2Affine) -> Self {
        Self(Bn254G2Prepared::from(g2.0))
    }
}

#[derive(Copy, Clone, Debug)]
pub struct MillerLoopResult(pub(crate) MillerLoopOutput<ArkBn254>);

impl Default for MillerLoopResult {
    fn default() -> Self {
        Self(MillerLoopOutput(Fq12::ZERO))
    }
}

impl DefaultIsZeroes for MillerLoopResult {}

impl ConditionallySelectable for MillerLoopResult {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(MillerLoopOutput(Fq12::new(
            fq6_conditionally_selectable(&a.0 .0.c0, &b.0 .0.c0, choice),
            fq6_conditionally_selectable(&a.0 .0.c1, &b.0 .0.c1, choice),
        )))
    }
}

impl AddAssign for MillerLoopResult {
    fn add_assign(&mut self, other: Self) {
        self.0 .0 += other.0 .0;
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = MillerLoopResult, RHS = MillerLoopResult, OUTPUT = MillerLoopResult);

impl pairing::MillerLoopResult for MillerLoopResult {
    type Gt = Gt;

    fn final_exponentiation(&self) -> Self::Gt {
        self.final_exponentiation()
    }
}

impl MillerLoopResult {
    pub fn final_exponentiation(&self) -> Gt {
        let res = ArkBn254::final_exponentiation(self.0).unwrap();
        Gt(res)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Gt(pub(crate) PairingOutput<ArkBn254>);

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

impl Neg for Gt {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(-self.0)
    }
}

impl Neg for &Gt {
    type Output = Gt;

    fn neg(self) -> Self::Output {
        Gt(-self.0)
    }
}

impl AddAssign for Gt {
    fn add_assign(&mut self, other: Self) {
        self.0 += other.0;
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = Gt, RHS = Gt, OUTPUT = Gt);

impl SubAssign for Gt {
    fn sub_assign(&mut self, other: Self) {
        self.0 -= other.0;
    }
}

ops_impl!(Sub, sub, -, SubAssign, sub_assign, -=, LHS = Gt, RHS = Gt, OUTPUT = Gt);

impl MulAssign<Scalar> for Gt {
    fn mul_assign(&mut self, other: Scalar) {
        self.0 *= other.0;
    }
}

ops_impl!(Mul, mul, *, MulAssign, mul_assign, *=, LHS = Gt, RHS = Scalar, OUTPUT = Gt);

impl<T: Borrow<Gt>> Sum<T> for Gt {
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        let mut sum = PairingOutput::<ArkBn254>::ZERO;
        for item in iter {
            sum += item.borrow().0;
        }
        Self(sum)
    }
}

impl Group for Gt {
    type Scalar = Scalar;

    fn random(mut rng: impl RngCore) -> Self {
        Self(PairingOutput(Fq12::rand(&mut rng)))
    }

    fn identity() -> Self {
        Self(PairingOutput::ZERO)
    }

    fn generator() -> Self {
        Self(PairingOutput(Fq12::GENERATOR))
    }

    fn is_identity(&self) -> Choice {
        Choice::from(if self.0.is_zero() { 1u8 } else { 0u8 })
    }

    fn double(&self) -> Self {
        Self(self.0.double())
    }
}

impl Gt {
    pub const ZERO: Self = Self(PairingOutput::ZERO);
}

impl PairingCurveAffine for G1Affine {
    type Pair = G2Affine;
    type PairingResult = Gt;

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult {
        Bn254::pairing(self, other)
    }
}

impl PairingCurveAffine for G2Affine {
    type Pair = G1Affine;
    type PairingResult = Gt;

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult {
        Bn254::pairing(other, self)
    }
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
