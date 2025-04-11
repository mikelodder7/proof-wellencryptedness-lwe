use super::Scalar;
use ark_bn254::{Fq, Fr, G1Affine as Bn254G1Affine, G1Projective as Bn254G1Projective};
use ark_ec::{AffineRepr, PrimeGroup as _};
use ark_ff::{AdditiveGroup, BigInt, BigInteger, Field, One, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use elliptic_curve::bigint::{
    impl_modulus, modular::constant_mod::ResidueParams, NonZero, U256, U384,
};
use elliptic_curve::group::cofactor::CofactorGroup;
use elliptic_curve::group::prime::{PrimeCurve, PrimeCurveAffine, PrimeGroup};
use elliptic_curve::group::{Curve, UncompressedEncoding, WnafGroup};
use elliptic_curve::hash2curve::{ExpandMsg, Expander};
use elliptic_curve::ops::MulByGenerator;
use elliptic_curve::point::AffineCoordinates;
use elliptic_curve::{
    generic_array::{
        typenum::{U32, U64},
        GenericArray,
    },
    group::GroupEncoding,
    Group,
};
use rand_core::RngCore;
use std::borrow::Borrow;
use std::iter::Sum;
use std::{
    fmt::{Display, Formatter, LowerHex, UpperHex},
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
use zeroize::DefaultIsZeroes;

pub type G1Repr = GenericArray<u8, U32>;
pub type G1UncompressedRepr = GenericArray<u8, U64>;

impl_modulus!(
    FpModulus,
    U256,
    "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47"
);

const MODULUS_U384: NonZero<U384> = NonZero::<U384>::const_new(FpModulus::MODULUS.resize()).0;

#[derive(Copy, Clone, Debug)]
pub struct G1Affine(pub Bn254G1Affine);

impl From<Bn254G1Affine> for G1Affine {
    fn from(pt: Bn254G1Affine) -> Self {
        Self(pt)
    }
}

impl From<&Bn254G1Affine> for G1Affine {
    fn from(pt: &Bn254G1Affine) -> Self {
        Self(*pt)
    }
}

impl From<G1Affine> for Bn254G1Affine {
    fn from(pt: G1Affine) -> Self {
        pt.0
    }
}

impl From<&G1Affine> for Bn254G1Affine {
    fn from(pt: &G1Affine) -> Self {
        pt.0
    }
}

impl From<G1Projective> for G1Affine {
    fn from(pt: G1Projective) -> Self {
        Self(pt.0.into())
    }
}

impl From<&G1Projective> for G1Affine {
    fn from(pt: &G1Projective) -> Self {
        Self(pt.0.into())
    }
}

impl Default for G1Affine {
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl DefaultIsZeroes for G1Affine {}

impl ConstantTimeEq for G1Affine {
    fn ct_eq(&self, other: &Self) -> Choice {
        let lhs_x = self
            .0
            .x()
            .expect("x coordinate is not defined")
            .into_bigint()
            .0;
        let rhs_x = other
            .0
            .x()
            .expect("x coordinate is not defined")
            .into_bigint()
            .0;
        let lhs_y = self
            .0
            .x()
            .expect("y coordinate is not defined")
            .into_bigint()
            .0;
        let rhs_y = other
            .0
            .x()
            .expect("y coordinate is not defined")
            .into_bigint()
            .0;
        let mut res = Choice::from(1u8);
        for i in 0..4 {
            res &= lhs_x[i].ct_eq(&rhs_x[i]);
            res &= lhs_y[i].ct_eq(&rhs_y[i]);
        }
        res
    }
}

impl ConditionallySelectable for G1Affine {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(Bn254G1Affine::new_unchecked(
            G1Projective::fq_conditional_select(
                &a.0.x().expect("x coordinate is not defined"),
                &b.0.x().expect("x coordinate is not defined"),
                choice,
            ),
            G1Projective::fq_conditional_select(
                &a.0.y().expect("y coordinate is not defined"),
                &b.0.y().expect("y coordinate is not defined"),
                choice,
            ),
        ))
    }
}

impl Eq for G1Affine {}

impl PartialEq for G1Affine {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl Display for G1Affine {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:x}", self)
    }
}

impl LowerHex for G1Affine {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut bytes = Vec::with_capacity(Self::UNCOMPRESSED_BYTES);
        self.0
            .serialize_uncompressed(&mut bytes)
            .expect("uncompressed bytes should not fail");

        write!(
            f,
            "G1Affine {{ x: 0x{}, y: 0x{} }}",
            hex::encode(&bytes[..32]),
            hex::encode(&bytes[32..])
        )
    }
}

impl UpperHex for G1Affine {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut bytes = Vec::with_capacity(Self::UNCOMPRESSED_BYTES);
        self.0
            .serialize_uncompressed(&mut bytes)
            .expect("uncompressed bytes should not fail");

        write!(
            f,
            "G1Affine {{ x: 0x{}, y: 0x{} }}",
            hex::encode_upper(&bytes[..32]),
            hex::encode_upper(&bytes[32..])
        )
    }
}

impl Neg for G1Affine {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(-self.0)
    }
}

impl Neg for &G1Affine {
    type Output = G1Affine;

    fn neg(self) -> Self::Output {
        G1Affine(-self.0)
    }
}

impl Add<G1Projective> for G1Affine {
    type Output = G1Projective;

    fn add(self, rhs: G1Projective) -> Self::Output {
        G1Projective(rhs.0 + self.0)
    }
}

ops_impl!(Add, add, +, LHS = G1Affine, RHS = G1Projective, OUTPUT = G1Projective);

impl Sub<G1Projective> for G1Affine {
    type Output = G1Projective;

    fn sub(self, rhs: G1Projective) -> Self::Output {
        G1Projective(-rhs.0 + self.0)
    }
}

ops_impl!(Sub, sub, -, LHS = G1Affine, RHS = G1Projective, OUTPUT = G1Projective);

impl Mul<Scalar> for G1Affine {
    type Output = G1Projective;

    fn mul(self, rhs: Scalar) -> Self::Output {
        G1Projective(self.0 * rhs.0)
    }
}

ops_impl!(Mul, mul, *, LHS = G1Affine, RHS = Scalar, OUTPUT = G1Projective);

impl Mul<G1Affine> for Scalar {
    type Output = G1Projective;

    fn mul(self, rhs: G1Affine) -> Self::Output {
        G1Projective(rhs.0 * self.0)
    }
}

ops_impl!(Mul, mul, *, LHS = Scalar, RHS = G1Affine, OUTPUT = G1Projective);

impl AffineCoordinates for G1Affine {
    type FieldRepr = G1Repr;

    fn x(&self) -> Self::FieldRepr {
        let mut repr = Vec::with_capacity(Self::COMPRESSED_BYTES);
        self.0
            .serialize_compressed(&mut repr)
            .expect("compressed bytes should not fail");
        G1Repr::clone_from_slice(&repr[..])
    }

    fn y_is_odd(&self) -> Choice {
        Choice::from(
            if self
                .0
                .y()
                .expect("y coordinate is not defined")
                .into_bigint()
                .is_odd()
            {
                1u8
            } else {
                0u8
            },
        )
    }
}

bytes_impl!(
    G1Affine,
    |p: &G1Affine| p.to_compressed(),
    |bytes: &[u8]| {
        Bn254G1Affine::deserialize_compressed(bytes)
            .map(Self)
            .map_err(|_| "failed to deserialize compressed G1Affine".to_string())
    }
);

serde_impl!(
    G1Affine,
    |p: &G1Affine| p.to_compressed(),
    |bytes: &[u8; G1Affine::COMPRESSED_BYTES]| {
        Bn254G1Affine::deserialize_compressed(&bytes[..])
            .map(Self)
            .map_err(|_| {
                serdect::serde::de::Error::custom(
                    "failed to deserialize compressed G1Affine".to_string(),
                )
            })
    },
    G1Affine::COMPRESSED_BYTES
);

impl GroupEncoding for G1Affine {
    type Repr = G1Repr;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        let pt = Bn254G1Affine::deserialize_compressed(&bytes[..]).ok();
        match pt {
            Some(pt) => CtOption::new(Self(pt), Choice::from(1u8)),
            None => CtOption::new(Self::IDENTITY, Choice::from(0u8)),
        }
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_bytes(bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.to_compressed()
    }
}

impl UncompressedEncoding for G1Affine {
    type Uncompressed = G1UncompressedRepr;

    fn from_uncompressed(bytes: &Self::Uncompressed) -> CtOption<Self> {
        let pt = Bn254G1Affine::deserialize_uncompressed(&bytes[..]).ok();
        match pt {
            Some(pt) => CtOption::new(Self(pt), Choice::from(1u8)),
            None => CtOption::new(Self::IDENTITY, Choice::from(0u8)),
        }
    }

    fn from_uncompressed_unchecked(bytes: &Self::Uncompressed) -> CtOption<Self> {
        let pt = Bn254G1Affine::deserialize_uncompressed(&bytes[..]).ok();
        match pt {
            Some(pt) => CtOption::new(Self(pt), Choice::from(1u8)),
            None => CtOption::new(Self::IDENTITY, Choice::from(0u8)),
        }
    }

    fn to_uncompressed(&self) -> Self::Uncompressed {
        self.to_uncompressed()
    }
}

impl G1Affine {
    pub const COMPRESSED_BYTES: usize = 32;
    pub const UNCOMPRESSED_BYTES: usize = 64;

    pub const IDENTITY: Self = Self(Bn254G1Affine::identity());

    pub const GENERATOR: Self = Self(Bn254G1Affine::new_unchecked(
        ark_bn254::g1::G1_GENERATOR_X,
        ark_bn254::g1::G1_GENERATOR_Y,
    ));

    pub fn from_compressed(bytes: &G1Repr) -> Option<Self> {
        Bn254G1Affine::deserialize_compressed(&bytes[..])
            .ok()
            .map(Self)
    }

    pub fn to_compressed(&self) -> G1Repr {
        let mut repr = Vec::with_capacity(Self::COMPRESSED_BYTES);
        self.0
            .serialize_compressed(&mut repr)
            .expect("compressed bytes should not fail");
        G1Repr::clone_from_slice(&repr[..])
    }

    pub fn from_uncompressed(bytes: &G1UncompressedRepr) -> Option<Self> {
        Bn254G1Affine::deserialize_uncompressed(&bytes[..])
            .ok()
            .map(Self)
    }

    pub fn to_uncompressed(&self) -> G1UncompressedRepr {
        let mut repr = Vec::with_capacity(Self::UNCOMPRESSED_BYTES);
        self.0
            .serialize_uncompressed(&mut repr)
            .expect("uncompressed bytes should not fail");
        G1UncompressedRepr::clone_from_slice(&repr[..])
    }

    pub fn is_identity(&self) -> Choice {
        Choice::from(if self.0.is_zero() { 1u8 } else { 0u8 })
    }

    pub fn is_on_curve(&self) -> Choice {
        Choice::from(if self.0.is_on_curve() { 1 } else { 0 })
    }
}

#[derive(Copy, Clone, Debug)]
pub struct G1Projective(pub Bn254G1Projective);

impl From<G1Affine> for G1Projective {
    fn from(pt: G1Affine) -> Self {
        Self(Bn254G1Projective::from(pt.0))
    }
}

impl From<&G1Affine> for G1Projective {
    fn from(pt: &G1Affine) -> Self {
        Self(Bn254G1Projective::from(pt.0))
    }
}

impl Default for G1Projective {
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl Display for G1Projective {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:x}", self)
    }
}

impl LowerHex for G1Projective {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:x}", G1Affine::from(self))
    }
}

impl UpperHex for G1Projective {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:X}", G1Affine::from(self))
    }
}

impl ConstantTimeEq for G1Projective {
    fn ct_eq(&self, other: &Self) -> Choice {
        let x1 = self.0.x * other.0.z;
        let x2 = other.0.x * self.0.z;

        let y1 = self.0.y * other.0.z;
        let y2 = other.0.y * self.0.z;

        let self_is_zero = self.0.is_zero();
        let other_is_zero = other.0.is_zero();

        let res = (self_is_zero & other_is_zero)
            | (!self_is_zero & !other_is_zero & (x1 == x2 && y1 == y2));
        Choice::from(if res { 1u8 } else { 0u8 })
    }
}

impl Eq for G1Projective {}

impl PartialEq for G1Projective {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl ConditionallySelectable for G1Projective {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(Bn254G1Projective::new_unchecked(
            Self::fq_conditional_select(&a.0.x, &b.0.x, choice),
            Self::fq_conditional_select(&a.0.y, &b.0.y, choice),
            Self::fq_conditional_select(&a.0.z, &b.0.z, choice),
        ))
    }
}

impl Neg for G1Projective {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(-self.0)
    }
}

impl Neg for &G1Projective {
    type Output = G1Projective;

    fn neg(self) -> Self::Output {
        G1Projective(-self.0)
    }
}

impl AddAssign for G1Projective {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = G1Projective, RHS = G1Projective, OUTPUT = G1Projective);

impl AddAssign<G1Affine> for G1Projective {
    fn add_assign(&mut self, rhs: G1Affine) {
        self.0 += rhs.0;
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = G1Projective, RHS = G1Affine, OUTPUT = G1Projective);

impl SubAssign for G1Projective {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
    }
}

ops_impl!(Sub, sub, -, SubAssign, sub_assign, -=, LHS = G1Projective, RHS = G1Projective, OUTPUT = G1Projective);

impl SubAssign<G1Affine> for G1Projective {
    fn sub_assign(&mut self, rhs: G1Affine) {
        self.0 -= rhs.0;
    }
}

ops_impl!(Sub, sub, -, SubAssign, sub_assign, -=, LHS = G1Projective, RHS = G1Affine, OUTPUT = G1Projective);

impl MulAssign<Scalar> for G1Projective {
    fn mul_assign(&mut self, rhs: Scalar) {
        self.0 *= rhs.0;
    }
}

ops_impl!(Mul, mul, *, MulAssign, mul_assign, *=, LHS = G1Projective, RHS = Scalar, OUTPUT = G1Projective);

bytes_impl!(
    G1Projective,
    |p: &G1Projective| p.to_compressed(),
    |bytes: &[u8]| {
        Bn254G1Projective::deserialize_compressed(bytes)
            .map(Self)
            .map_err(|_| "failed to deserialize compressed G1Projective".to_string())
    }
);

serde_impl!(
    G1Projective,
    |p: &G1Projective| p.to_compressed(),
    |bytes: &[u8; G1Projective::COMPRESSED_BYTES]| {
        Bn254G1Projective::deserialize_compressed(&bytes[..])
            .map(Self)
            .map_err(|_| {
                serdect::serde::de::Error::custom(
                    "failed to deserialize compressed G1Projective".to_string(),
                )
            })
    },
    G1Projective::COMPRESSED_BYTES
);

impl MulByGenerator for G1Projective {}

impl<T: Borrow<G1Projective>> Sum<T> for G1Projective {
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        let mut sum = Bn254G1Projective::default();
        for item in iter {
            sum += item.borrow().0;
        }
        Self(sum)
    }
}

impl Group for G1Projective {
    type Scalar = Scalar;

    fn random(mut rng: impl RngCore) -> Self {
        Self(Bn254G1Projective::rand(&mut rng))
    }

    fn identity() -> Self {
        Self::IDENTITY
    }

    fn generator() -> Self {
        Self::GENERATOR
    }

    fn is_identity(&self) -> Choice {
        Choice::from(if self.0.is_zero() { 1u8 } else { 0u8 })
    }

    fn double(&self) -> Self {
        Self(self.0.double())
    }
}

impl GroupEncoding for G1Projective {
    type Repr = G1Repr;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        let pt = Bn254G1Projective::deserialize_compressed(&bytes[..]).ok();
        match pt {
            Some(pt) => CtOption::new(Self(pt), Choice::from(1u8)),
            None => CtOption::new(Self::IDENTITY, Choice::from(0u8)),
        }
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_bytes(bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.to_compressed()
    }
}

impl PrimeGroup for G1Projective {}

impl Curve for G1Projective {
    type AffineRepr = G1Affine;

    fn to_affine(&self) -> Self::AffineRepr {
        self.into()
    }
}

impl PrimeCurve for G1Projective {
    type Affine = G1Affine;
}

impl PrimeCurveAffine for G1Affine {
    type Scalar = Scalar;
    type Curve = G1Projective;

    fn identity() -> Self {
        Self::IDENTITY
    }

    fn generator() -> Self {
        Self::GENERATOR
    }

    fn is_identity(&self) -> Choice {
        self.is_identity()
    }

    fn to_curve(&self) -> Self::Curve {
        self.into()
    }
}

impl DefaultIsZeroes for G1Projective {}

impl UncompressedEncoding for G1Projective {
    type Uncompressed = G1UncompressedRepr;

    fn from_uncompressed(bytes: &Self::Uncompressed) -> CtOption<Self> {
        match Self::from_uncompressed(bytes) {
            Some(pt) => CtOption::new(pt, Choice::from(1u8)),
            None => CtOption::new(Self::IDENTITY, Choice::from(0u8)),
        }
    }

    fn from_uncompressed_unchecked(bytes: &Self::Uncompressed) -> CtOption<Self> {
        match Self::from_uncompressed(bytes) {
            Some(pt) => CtOption::new(pt, Choice::from(1u8)),
            None => CtOption::new(Self::IDENTITY, Choice::from(0u8)),
        }
    }

    fn to_uncompressed(&self) -> Self::Uncompressed {
        self.to_uncompressed()
    }
}

impl CofactorGroup for G1Projective {
    type Subgroup = Self;

    fn clear_cofactor(&self) -> Self::Subgroup {
        *self
    }

    fn into_subgroup(self) -> CtOption<Self::Subgroup> {
        CtOption::new(self, Choice::from(1u8))
    }

    fn is_torsion_free(&self) -> Choice {
        Choice::from(if self.0.mul_bigint(&Fr::MODULUS.0).is_zero() {
            1u8
        } else {
            0u8
        })
    }
}

impl WnafGroup for G1Projective {
    fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        const RECOMMENDATIONS: [usize; 12] =
            [1, 3, 7, 20, 43, 120, 273, 563, 1630, 3128, 7933, 62569];

        let mut ret = 4;
        for r in &RECOMMENDATIONS {
            if num_scalars > *r {
                ret += 1;
            } else {
                break;
            }
        }

        ret
    }
}

impl G1Projective {
    pub const COMPRESSED_BYTES: usize = 32;
    pub const UNCOMPRESSED_BYTES: usize = 64;
    pub const IDENTITY: Self = Self(Bn254G1Projective::new_unchecked(
        Fq::ZERO,
        Fq::ZERO,
        Fq::ZERO,
    ));
    pub const GENERATOR: Self = Self(Bn254G1Projective::new_unchecked(
        ark_bn254::g1::G1_GENERATOR_X,
        ark_bn254::g1::G1_GENERATOR_Y,
        Fq::ONE,
    ));

    pub fn to_compressed(&self) -> G1Repr {
        G1Affine::from(self).to_compressed()
    }

    pub fn from_compressed(bytes: &G1Repr) -> Option<Self> {
        G1Affine::from_compressed(bytes).map(|pt| pt.into())
    }

    pub fn to_uncompressed(&self) -> G1UncompressedRepr {
        G1Affine::from(self).to_uncompressed()
    }

    pub fn from_uncompressed(bytes: &G1UncompressedRepr) -> Option<Self> {
        G1Affine::from_uncompressed(bytes).map(G1Projective::from)
    }

    pub fn is_on_curve(&self) -> Choice {
        Choice::from(if Bn254G1Affine::from(self.0).is_on_curve() {
            1u8
        } else {
            0u8
        })
    }

    pub fn hash<X>(msg: &[u8], dst: &[u8]) -> Self
    where
        X: for<'a> ExpandMsg<'a>,
    {
        let u = Self::hash_fq::<X>(msg, dst);
        let q0 = Self::map_to_curve(&u[0]);
        let q1 = Self::map_to_curve(&u[1]);

        q0 + q1
    }

    fn hash_fq<X>(msg: &[u8], dst: &[u8]) -> [Fq; 2]
    where
        X: for<'a> ExpandMsg<'a>,
    {
        let dst = [dst];
        let mut random_bytes = [0u8; 96];
        let mut expander = X::expand_message(&[msg], &dst, 96).expect("expansion should not fail");
        expander.fill_bytes(&mut random_bytes);
        [
            Self::fq_from_okm(&random_bytes[..48]),
            Self::fq_from_okm(&random_bytes[48..]),
        ]
    }

    pub(crate) fn fq_from_okm(okm: &[u8]) -> Fq {
        debug_assert_eq!(okm.len(), 48);

        let inner: U256 = (U384::from_be_slice(okm) % MODULUS_U384).resize();
        Fq::new(BigInt::new(inner.to_words()))
    }

    pub(crate) fn fq_is_square(u: &Fq) -> Choice {
        let res = u.pow(Fq::MODULUS_MINUS_ONE_DIV_TWO.0);
        Choice::from(if res.is_zero() | res.is_one() {
            1u8
        } else {
            0u8
        })
    }

    pub(crate) fn fq_conditional_select(a: &Fq, b: &Fq, choice: Choice) -> Fq {
        let mut res = [0u64; 4];
        let a = a.into_bigint().0;
        let b = b.into_bigint().0;

        for i in 0..4 {
            res[i] = u64::conditional_select(&a[i], &b[i], choice);
        }
        Fq::new(BigInt::new(res))
    }

    pub(crate) fn fq_sgn0(u: &Fq) -> Choice {
        let res = u.into_bigint().0[0] & 1;
        Choice::from(res as u8)
    }

    pub(crate) fn fq_conditional_negate(u: &Fq, choice: Choice) -> Fq {
        let neg_u = -*u;
        Self::fq_conditional_select(u, &neg_u, choice)
    }

    fn map_to_curve(u: &Fq) -> Self {
        const Z: Fq = Fq::ONE;
        const THREE: Fq = Fq::new(BigInt::new([3, 0, 0, 0]));
        const C1: Fq = Fq::new(BigInt::new([4, 0, 0, 0]));
        const C2: Fq = Fq::new(BigInt::new([
            0x9e10460b6c3e7ea3,
            0xcbc0b548b438e546,
            0xdc2822db40c0ac2e,
            0x183227397098d014,
        ]));
        const C3: Fq = Fq::new(BigInt::new([
            0x5d8d1cc5dffffffa,
            0x53c98fc6b36d713d,
            0x6789af3a83522eb3,
            0x0000000000000001,
        ]));
        const C4: Fq = Fq::new(BigInt::new([
            0x69602eb24829a9bd,
            0xdd2b2385cd7b4384,
            0xe81ac1e7808072c9,
            0x10216f7ba065e00d,
        ]));

        let mut tv1 = u.square(); //    1.  tv1 = u²
        tv1 *= C1; //    2.  tv1 = tv1 * c1
        let tv2 = Fq::ONE + tv1; //    3.  tv2 = 1 + tv1
        tv1 = Fq::ONE - tv1; //    4.  tv1 = 1 - tv1
        let mut tv3 = tv1 * tv2; //    5.  tv3 = tv1 * tv2

        tv3 = tv3.inverse().expect("to not be zero"); //    6.  tv3 = inv0(tv3)
        let mut tv4 = *u * tv1; //    7.  tv4 = u * tv1
        tv4 *= tv3; //    8.  tv4 = tv4 * tv3
        tv4 *= C3; //    9.  tv4 = tv4 * c3
        let x1 = C2 - tv4; //    10.  x1 = c2 - tv4

        let mut gx1 = x1.square(); //    11. gx1 = x1²
                                   //12. gx1 = gx1 + A  It is crucial to include this step if the curve has nonzero A coefficient.
        gx1 *= x1; //    13. gx1 = gx1 * x1
        gx1 += THREE; //    14. gx1 = gx1 + B

        // let gx1NotSquare: i32 = if gx1.legendre().is_qr() {0} else {-1};    //    15.  e1 = is_square(gx1)
        // gx1NotSquare = 0 if gx1 is a square, -1 otherwise

        let x2 = C2 + tv4; //    16.  x2 = c2 + tv4
        let mut gx2 = x2.square(); //    17. gx2 = x2²
                                   //    18. gx2 = gx2 + A     See line 12
        gx2 *= x2; //    19. gx2 = gx2 * x2
        gx2 += THREE; //    20. gx2 = gx2 + B

        let mut x3 = tv2.square(); //    22.  x3 = tv2²
        x3 *= tv3; //    23.  x3 = x3 * tv3
        x3 = x3.square(); //    24.  x3 = x3²
        x3 *= C4; //    25.  x3 = x3 * c4

        x3 += Z; //    26.  x3 = x3 + Z

        let e1 = Self::fq_is_square(&gx1);
        let mut x = Self::fq_conditional_select(&x3, &x1, e1); //    27.   x = CMOV(x3, x1, e1)   # x = x1 if gx1 is square, else x = x3

        x = Self::fq_conditional_select(&x, &x2, Self::fq_is_square(&gx2) & !e1); //    28.   x = CMOV(x, x2, e2)    # x = x2 if gx2 is square and gx1 is not
                                                                                  // Select x2 iff gx2 is square and gx1 is not, iff gx1SquareOrGx2Not = 0

        let mut gx = x.square(); //    29.  gx = x²
                                 //    30.  gx = gx + A
        gx *= x; //    31.  gx = gx * x
        gx += THREE; //    32.  gx = gx + B

        let mut y = gx.sqrt().expect("sqrt to work"); //    33.   y = sqrt(gx)

        let e3 = Self::fq_sgn0(u) ^ Self::fq_sgn0(&y);

        y = Self::fq_conditional_negate(&y, e3);

        Self(Bn254G1Projective::new(x, y, Fq::ONE))
    }
}
