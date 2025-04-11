use super::{G1Projective, Scalar};
use std::borrow::Borrow;
use std::fmt::{Display, Formatter, LowerHex, UpperHex};
use std::iter::Sum;

use ark_bn254::{Fq, Fq2, Fr, G2Affine as Bn254G2Affine, G2Projective as Bn254G2Projective};
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ec::{AffineRepr, PrimeGroup as _};
use ark_ff::{AdditiveGroup, BigInt, BigInteger, Field, One, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use blsful::inner_types::{
    CofactorGroup, Group, GroupEncoding, PrimeCurve, PrimeCurveAffine, PrimeGroup,
    UncompressedEncoding,
};
use elliptic_curve::bigint::U256;
use elliptic_curve::generic_array::typenum::{U128, U64};
use elliptic_curve::generic_array::GenericArray;
use elliptic_curve::group::{Curve, WnafGroup};
use elliptic_curve::hash2curve::{ExpandMsg, Expander};
use elliptic_curve::ops::MulByGenerator;
use elliptic_curve::point::AffineCoordinates;
use rand_core::RngCore;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
use zeroize::DefaultIsZeroes;

/// The representation of the compressed representation of a G2 element, in bytes.
pub type G2Repr = GenericArray<u8, U64>;
/// The representation of the uncompressed representation of a G2 element, in bytes.
pub type G2UncompressedRepr = GenericArray<u8, U128>;

#[derive(Copy, Clone, Debug)]
pub struct G2Affine(pub Bn254G2Affine);

impl From<Bn254G2Affine> for G2Affine {
    fn from(g: Bn254G2Affine) -> Self {
        Self(g)
    }
}

impl From<&Bn254G2Affine> for G2Affine {
    fn from(g: &Bn254G2Affine) -> Self {
        Self(*g)
    }
}

impl From<G2Affine> for Bn254G2Affine {
    fn from(g: G2Affine) -> Self {
        g.0
    }
}

impl From<&G2Affine> for Bn254G2Affine {
    fn from(g: &G2Affine) -> Self {
        g.0
    }
}

impl From<G2Projective> for G2Affine {
    fn from(g: G2Projective) -> Self {
        Self(g.0.into())
    }
}

impl From<&G2Projective> for G2Affine {
    fn from(g: &G2Projective) -> Self {
        Self(g.0.into())
    }
}

impl Default for G2Affine {
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl DefaultIsZeroes for G2Affine {}

impl ConstantTimeEq for G2Affine {
    fn ct_eq(&self, other: &Self) -> Choice {
        let x = self.0.x().expect("x coordinate is not defined");
        let y = self.0.y().expect("y coordinate is not defined");
        let rhs_x = other.0.x().expect("x coordinate is not defined");
        let rhs_y = other.0.y().expect("y coordinate is not defined");

        let x_c0 = x.c0.into_bigint().0;
        let x_c1 = x.c1.into_bigint().0;
        let y_c0 = y.c0.into_bigint().0;
        let y_c1 = y.c1.into_bigint().0;

        let rhs_x_c0 = rhs_x.c0.into_bigint().0;
        let rhs_x_c1 = rhs_x.c1.into_bigint().0;
        let rhs_y_c0 = rhs_y.c0.into_bigint().0;
        let rhs_y_c1 = rhs_y.c1.into_bigint().0;

        let mut res = Choice::from(1u8);
        for i in 0..4 {
            res &= x_c0[i].ct_eq(&rhs_x_c0[i]);
            res &= x_c1[i].ct_eq(&rhs_x_c1[i]);
            res &= y_c0[i].ct_eq(&rhs_y_c0[i]);
            res &= y_c1[i].ct_eq(&rhs_y_c1[i]);
        }

        res
    }
}

impl Eq for G2Affine {}

impl PartialEq for G2Affine {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl Display for G2Affine {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:x}", self)
    }
}

impl LowerHex for G2Affine {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut bytes = Vec::with_capacity(Self::UNCOMPRESSED_BYTES);
        self.0
            .serialize_uncompressed(&mut bytes)
            .expect("uncompressed bytes should not fail");

        write!(
            f,
            "G2Affine {{ x: 0x{}, y: 0x{} }}",
            hex::encode(&bytes[..64]),
            hex::encode(&bytes[64..])
        )
    }
}

impl UpperHex for G2Affine {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut bytes = Vec::with_capacity(Self::UNCOMPRESSED_BYTES);
        self.0
            .serialize_uncompressed(&mut bytes)
            .expect("uncompressed bytes should not fail");

        write!(
            f,
            "G2Affine {{ x: 0x{}, y: 0x{} }}",
            hex::encode_upper(&bytes[..64]),
            hex::encode_upper(&bytes[64..])
        )
    }
}

impl ConditionallySelectable for G2Affine {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(Bn254G2Affine::new_unchecked(
            G2Projective::fq2_conditional_select(
                &a.0.x().expect("x coordinate is not defined"),
                &b.0.x().expect("x coordinate is not defined"),
                choice,
            ),
            G2Projective::fq2_conditional_select(
                &a.0.y().expect("y coordinate is not defined"),
                &b.0.y().expect("y coordinate is not defined"),
                choice,
            ),
        ))
    }
}

impl Neg for G2Affine {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(-self.0)
    }
}

impl Neg for &G2Affine {
    type Output = G2Affine;

    fn neg(self) -> Self::Output {
        G2Affine(-self.0)
    }
}

impl Add<G2Projective> for G2Affine {
    type Output = G2Projective;

    fn add(self, rhs: G2Projective) -> Self::Output {
        G2Projective(rhs.0 + self.0)
    }
}

ops_impl!(Add, add, +, LHS = G2Affine, RHS = G2Projective, OUTPUT = G2Projective);

impl Sub<G2Projective> for G2Affine {
    type Output = G2Projective;

    fn sub(self, rhs: G2Projective) -> Self::Output {
        G2Projective(-rhs.0 + self.0)
    }
}

ops_impl!(Sub, sub, -, LHS = G2Affine, RHS = G2Projective, OUTPUT = G2Projective);

impl Mul<Scalar> for G2Affine {
    type Output = G2Projective;

    fn mul(self, rhs: Scalar) -> Self::Output {
        G2Projective(self.0 * rhs.0)
    }
}

ops_impl!(Mul, mul, *, LHS = G2Affine, RHS = Scalar, OUTPUT = G2Projective);

impl Mul<G2Affine> for Scalar {
    type Output = G2Projective;

    fn mul(self, rhs: G2Affine) -> Self::Output {
        G2Projective(rhs.0 * self.0)
    }
}

ops_impl!(Mul, mul, *, LHS = Scalar, RHS = G2Affine, OUTPUT = G2Projective);

impl AffineCoordinates for G2Affine {
    type FieldRepr = G2Repr;

    fn x(&self) -> Self::FieldRepr {
        let mut repr = Vec::with_capacity(Self::COMPRESSED_BYTES);
        self.0
            .serialize_compressed(&mut repr)
            .expect("compressed bytes should not fail");
        G2Repr::clone_from_slice(&repr[..])
    }

    fn y_is_odd(&self) -> Choice {
        let y = self.0.y().expect("y coordinate is not defined");
        let y_c0 = y.c0.into_bigint();
        let y_c1 = y.c1.into_bigint();

        let res = if y_c0.is_zero() {
            y_c1.is_odd()
        } else {
            y_c0.is_odd()
        };
        Choice::from(if res { 1u8 } else { 0u8 })
    }
}

bytes_impl!(
    G2Affine,
    |p: &G2Affine| p.to_compressed(),
    |bytes: &[u8]| {
        Bn254G2Affine::deserialize_compressed(bytes)
            .map(Self)
            .map_err(|_| "failed to deserialize compressed G2Affine".to_string())
    }
);

serde_impl!(
    G2Affine,
    |p: &G2Affine| p.to_compressed(),
    |bytes: &[u8; G2Affine::COMPRESSED_BYTES]| {
        Bn254G2Affine::deserialize_compressed(&bytes[..])
            .map(Self)
            .map_err(|_| {
                serdect::serde::de::Error::custom(
                    "failed to deserialize compressed G2Affine".to_string(),
                )
            })
    },
    G2Affine::COMPRESSED_BYTES
);

impl GroupEncoding for G2Affine {
    type Repr = G2Repr;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        let pt = Bn254G2Affine::deserialize_compressed(&bytes[..]).ok();
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

impl UncompressedEncoding for G2Affine {
    type Uncompressed = G2UncompressedRepr;

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

impl G2Affine {
    pub const COMPRESSED_BYTES: usize = 64;
    pub const UNCOMPRESSED_BYTES: usize = 128;
    pub const IDENTITY: Self = Self(Bn254G2Affine::identity());
    pub const GENERATOR: Self = Self(Bn254G2Affine::new_unchecked(
        ark_bn254::g2::G2_GENERATOR_X,
        ark_bn254::g2::G2_GENERATOR_Y,
    ));

    pub fn from_compressed(bytes: &G2Repr) -> Option<Self> {
        Bn254G2Affine::deserialize_compressed(&bytes[..])
            .ok()
            .map(Self)
    }

    pub fn to_compressed(&self) -> G2Repr {
        let mut repr = Vec::with_capacity(Self::COMPRESSED_BYTES);
        self.0
            .serialize_compressed(&mut repr)
            .expect("compressed bytes should not fail");
        G2Repr::clone_from_slice(&repr[..])
    }

    pub fn from_uncompressed(bytes: &G2UncompressedRepr) -> Option<Self> {
        Bn254G2Affine::deserialize_uncompressed(&bytes[..])
            .ok()
            .map(Self)
    }

    pub fn to_uncompressed(&self) -> G2UncompressedRepr {
        let mut repr = Vec::with_capacity(Self::UNCOMPRESSED_BYTES);
        self.0
            .serialize_uncompressed(&mut repr)
            .expect("uncompressed bytes should not fail");
        G2UncompressedRepr::clone_from_slice(&repr[..])
    }

    pub fn is_identity(&self) -> Choice {
        Choice::from(if self.0.is_zero() { 1u8 } else { 0u8 })
    }

    pub fn is_on_curve(&self) -> Choice {
        Choice::from(if self.0.is_on_curve() { 1 } else { 0 })
    }
}

#[derive(Copy, Clone, Debug)]
pub struct G2Projective(pub Bn254G2Projective);

impl From<G2Affine> for G2Projective {
    fn from(pt: G2Affine) -> Self {
        Self(Bn254G2Projective::from(pt.0))
    }
}

impl From<&G2Affine> for G2Projective {
    fn from(pt: &G2Affine) -> Self {
        Self(Bn254G2Projective::from(pt.0))
    }
}

impl Default for G2Projective {
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl Display for G2Projective {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:x}", self)
    }
}

impl LowerHex for G2Projective {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:x}", G2Affine::from(self))
    }
}

impl UpperHex for G2Projective {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:X}", G2Affine::from(self))
    }
}

impl ConstantTimeEq for G2Projective {
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

impl Eq for G2Projective {}

impl PartialEq for G2Projective {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl ConditionallySelectable for G2Projective {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(Bn254G2Projective::new_unchecked(
            Self::fq2_conditional_select(&a.0.x, &b.0.x, choice),
            Self::fq2_conditional_select(&a.0.y, &b.0.y, choice),
            Self::fq2_conditional_select(&a.0.z, &b.0.z, choice),
        ))
    }
}

impl Neg for G2Projective {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(-self.0)
    }
}

impl Neg for &G2Projective {
    type Output = G2Projective;

    fn neg(self) -> Self::Output {
        G2Projective(-self.0)
    }
}

impl AddAssign for G2Projective {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = G2Projective, RHS = G2Projective, OUTPUT = G2Projective);

impl AddAssign<G2Affine> for G2Projective {
    fn add_assign(&mut self, rhs: G2Affine) {
        self.0 += rhs.0;
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = G2Projective, RHS = G2Affine, OUTPUT = G2Projective);

impl SubAssign for G2Projective {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
    }
}

ops_impl!(Sub, sub, -, SubAssign, sub_assign, -=, LHS = G2Projective, RHS = G2Projective, OUTPUT = G2Projective);

impl SubAssign<G2Affine> for G2Projective {
    fn sub_assign(&mut self, rhs: G2Affine) {
        self.0 -= rhs.0;
    }
}

ops_impl!(Sub, sub, -, SubAssign, sub_assign, -=, LHS = G2Projective, RHS = G2Affine, OUTPUT = G2Projective);

impl MulAssign<Scalar> for G2Projective {
    fn mul_assign(&mut self, rhs: Scalar) {
        self.0 *= rhs.0;
    }
}

ops_impl!(Mul, mul, *, MulAssign, mul_assign, *=, LHS = G2Projective, RHS = Scalar, OUTPUT = G2Projective);

bytes_impl!(
    G2Projective,
    |p: &G2Projective| p.to_compressed(),
    |bytes: &[u8]| {
        Bn254G2Projective::deserialize_compressed(bytes)
            .map(Self)
            .map_err(|_| "failed to deserialize compressed G2Projective".to_string())
    }
);

serde_impl!(
    G2Projective,
    |p: &G2Projective| p.to_compressed(),
    |bytes: &[u8; G2Projective::COMPRESSED_BYTES]| {
        Bn254G2Projective::deserialize_compressed(&bytes[..])
            .map(Self)
            .map_err(|_| {
                serdect::serde::de::Error::custom(
                    "failed to deserialize compressed G2Projective".to_string(),
                )
            })
    },
    G2Projective::COMPRESSED_BYTES
);

impl MulByGenerator for G2Projective {}

impl<T: Borrow<G2Projective>> Sum<T> for G2Projective {
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        let mut sum = Bn254G2Projective::default();
        for item in iter {
            sum += item.borrow().0;
        }
        Self(sum)
    }
}

impl Group for G2Projective {
    type Scalar = Scalar;

    fn random(mut rng: impl RngCore) -> Self {
        Self(Bn254G2Projective::rand(&mut rng))
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

impl GroupEncoding for G2Projective {
    type Repr = G2Repr;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        let pt = Bn254G2Projective::deserialize_compressed(&bytes[..]).ok();
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

impl PrimeGroup for G2Projective {}

impl Curve for G2Projective {
    type AffineRepr = G2Affine;

    fn to_affine(&self) -> Self::AffineRepr {
        self.into()
    }
}

impl PrimeCurve for G2Projective {
    type Affine = G2Affine;
}

impl PrimeCurveAffine for G2Affine {
    type Scalar = Scalar;
    type Curve = G2Projective;

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

impl DefaultIsZeroes for G2Projective {}

impl UncompressedEncoding for G2Projective {
    type Uncompressed = G2UncompressedRepr;

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

impl CofactorGroup for G2Projective {
    type Subgroup = Self;

    fn clear_cofactor(&self) -> Self::Subgroup {
        const COFACTOR: Fr = Fr::new(BigInt::new([
            0x345f2299c0f9fa8d,
            0x06ceecda572a2489,
            0xb85045b68181585e,
            0x30644e72e131a029,
        ]));
        Self(self.0 * COFACTOR)
    }

    fn into_subgroup(self) -> CtOption<Self::Subgroup> {
        CtOption::new(self.clear_cofactor(), Choice::from(1u8))
    }

    fn is_torsion_free(&self) -> Choice {
        Choice::from(if self.0.mul_bigint(&Fr::MODULUS.0).is_zero() {
            1u8
        } else {
            0u8
        })
    }
}

impl WnafGroup for G2Projective {
    fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        const RECOMMENDATIONS: [usize; 11] = [1, 3, 8, 20, 47, 126, 260, 826, 1501, 4555, 84071];

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

impl G2Projective {
    pub const COMPRESSED_BYTES: usize = 64;
    pub const UNCOMPRESSED_BYTES: usize = 128;
    pub const IDENTITY: Self = Self(Bn254G2Projective::new_unchecked(
        Fq2::ZERO,
        Fq2::ZERO,
        Fq2::ZERO,
    ));
    pub const GENERATOR: Self = Self(Bn254G2Projective::new_unchecked(
        ark_bn254::g2::G2_GENERATOR_X,
        ark_bn254::g2::G2_GENERATOR_Y,
        Fq2::ONE,
    ));

    pub fn to_compressed(&self) -> G2Repr {
        G2Affine::from(self).to_compressed()
    }

    pub fn from_compressed(bytes: &G2Repr) -> Option<Self> {
        G2Affine::from_compressed(bytes).map(|pt| pt.into())
    }

    pub fn to_uncompressed(&self) -> G2UncompressedRepr {
        G2Affine::from(self).to_uncompressed()
    }

    pub fn from_uncompressed(bytes: &G2UncompressedRepr) -> Option<Self> {
        G2Affine::from_uncompressed(bytes).map(G2Projective::from)
    }

    pub fn is_on_curve(&self) -> Choice {
        Choice::from(if Bn254G2Affine::from(self.0).is_on_curve() {
            1u8
        } else {
            0u8
        })
    }

    pub fn hash<X>(msg: &[u8], dst: &[u8]) -> Self
    where
        X: for<'a> ExpandMsg<'a>,
    {
        let u = Self::hash_fq2::<X>(msg, dst);
        let q0 = Self::map_to_curve(&u[0]);
        let q1 = Self::map_to_curve(&u[1]);

        q0 + q1
    }

    fn hash_fq2<X>(msg: &[u8], dst: &[u8]) -> [Fq2; 2]
    where
        X: for<'a> ExpandMsg<'a>,
    {
        let dst = [dst];
        let mut random_bytes = [0u8; 192];
        let mut expander = X::expand_message(&[msg], &dst, 192).expect("expansion should not fail");
        expander.fill_bytes(&mut random_bytes);
        [
            Self::fq2_from_okm(&random_bytes[..96]),
            Self::fq2_from_okm(&random_bytes[96..]),
        ]
    }

    pub(crate) fn fq2_from_okm(okm: &[u8]) -> Fq2 {
        debug_assert_eq!(okm.len(), 96);

        let c0 = G1Projective::fq_from_okm(&okm[..48]);
        let c1 = G1Projective::fq_from_okm(&okm[48..]);
        Fq2::new(c0, c1)
    }

    pub(crate) fn fq2_is_square(u: &Fq2) -> Choice {
        let res = (u.c0.square() + u.c1.square()).pow(Fq::MODULUS_MINUS_ONE_DIV_TWO.0);
        Choice::from(if res.is_zero() | res.is_one() {
            1u8
        } else {
            0u8
        })
    }

    pub(crate) fn fq2_conditional_select(a: &Fq2, b: &Fq2, choice: Choice) -> Fq2 {
        let mut res_c0 = [0; 4];
        let mut res_c1 = [0; 4];

        let a_c0 = a.c0.into_bigint().0;
        let a_c1 = a.c1.into_bigint().0;

        let b_c0 = b.c0.into_bigint().0;
        let b_c1 = b.c1.into_bigint().0;

        for i in 0..4 {
            res_c0[i] = u64::conditional_select(&a_c0[i], &b_c0[i], choice);
            res_c1[i] = u64::conditional_select(&a_c1[i], &b_c1[i], choice);
        }

        Fq2::new(Fq::new(BigInt::new(res_c0)), Fq::new(BigInt::new(res_c1)))
    }

    pub(crate) fn fq2_sgn0(u: &Fq2) -> Choice {
        let c0 = u.c0.into_bigint();
        let c1 = u.c1.into_bigint();

        let res = if c0.is_zero() {
            c1.is_odd()
        } else {
            c0.is_odd()
        };
        Choice::from(if res { 1u8 } else { 0u8 })
    }

    pub(crate) fn fq2_conditional_negate(u: &Fq2, choice: Choice) -> Fq2 {
        let neg_a = -*u;

        Self::fq2_conditional_select(u, &neg_a, choice)
    }

    fn map_to_curve(u: &Fq2) -> Self {
        const Z: Fq2 = Fq2::ONE;
        const C1: Fq2 = Fq2::new(
            Fq::new(BigInt::new(
                U256::from_be_hex(
                    "2b149d40ceb8aaae81be18991be06ac3b5b4c5e559dbefa33267e6dc24a138e6",
                )
                .to_words(),
            )),
            Fq::new(BigInt::new(
                U256::from_be_hex(
                    "009713b03af0fed4cd2cafadeed8fdf4a74fa084e52d1852e4a2bd0685c315d2",
                )
                .to_words(),
            )),
        );
        const C2: Fq2 = Fq2::new(
            Fq::new(BigInt::new(
                U256::from_be_hex(
                    "183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e10460b6c3e7ea3",
                )
                .to_words(),
            )),
            Fq::ZERO,
        );
        const C3: Fq2 = Fq2::new(
            Fq::new(BigInt::new(
                U256::from_be_hex(
                    "29fd332ab7260112b801fa95b21af64e2e6da55f90a3e510fcbe57377b5ca1ec",
                )
                .to_words(),
            )),
            Fq::new(BigInt::new(
                U256::from_be_hex(
                    "303d1eff1426764bf8408aee24ba0b865e76f77b1267a846b1e9154d01565034",
                )
                .to_words(),
            )),
        );
        const C4: Fq2 = Fq2::new(
            Fq::new(BigInt::new(
                U256::from_be_hex(
                    "17365bbe63b1d2078632fe0eb2ac5a41b4e6a9c08b98676721010b008d4eaf99",
                )
                .to_words(),
            )),
            Fq::new(BigInt::new(
                U256::from_be_hex(
                    "0f57ffe5fc79e19cd689d7aa4209cad8fe164d7f4694786b388732a995d03755",
                )
                .to_words(),
            )),
        );

        let mut tv1 = u.square(); //    1.  tv1 = u²
        tv1 *= C1; //    2.  tv1 = tv1 * c1
        let tv2 = Fq2::ONE + tv1; //    3.  tv2 = 1 + tv1
        tv1 = Fq2::ONE - tv1; //    4.  tv1 = 1 - tv1
        let mut tv3 = tv1 * tv2; //    5.  tv3 = tv1 * tv2
        tv3 = tv3.inverse().expect("non zero"); //    6.  tv3 = inv0(tv3)
        let mut tv4 = u * tv1; //    7.  tv4 = u * tv1
        tv4 *= tv3; //    8.  tv4 = tv4 * tv3
        tv4 *= C3; //    9.  tv4 = tv4 * c3
        let x1 = C2 - tv4; //    10.  x1 = c2 - tv4
        let mut gx1 = x1.square(); //    11. gx1 = x1²
                                   //    12. gx1 = gx1 + A     All curves in gnark-crypto have A=0 (j-invariant=0). It is crucial to include this step if the curve has nonzero A coefficient.
        gx1 *= x1; //    13. gx1 = gx1 * x1
        gx1 += ark_bn254::g2::Config::COEFF_B; //    14. gx1 = gx1 + B
        let x2 = C2 + tv4; //    15.  x2 = c2 + tv4
        let mut gx2 = x2.square(); //    16. gx2 = x2²
                                   //    17. gx2 = gx2 + A (see 12.)
        gx2 *= x2; //    18. gx2 = gx2 * x2
        gx2 += ark_bn254::g2::Config::COEFF_B; //    19. gx2 = gx2 + B
        let mut x3 = tv2.square(); //    20.  x3 = tv2²
        x3 *= tv3; //    21.  x3 = x3 * tv3
        x3 = x3.square(); //    22.  x3 = x3²
        x3 *= C4; //    23.  x3 = x3 * c4
        x3 += Z; //    24.  x3 = x3 + Z
        let e1 = Self::fq2_is_square(&gx1);
        let mut x = Self::fq2_conditional_select(&x3, &x1, e1); //    25.   x = CMOV(x3, x1, e1)   # x = x1 if gx1 is square, else x = x3
        x = Self::fq2_conditional_select(&x, &x2, Self::fq2_is_square(&gx2) & !e1); //    26.   x = CMOV(x, x2, e2)    # x = x2 if gx2 is square and gx1 is not
        let mut gx = x.square(); //    27.  gx = x²
                                 //    28.  gx = gx + A
        gx *= x; //    29.  gx = gx * x
        gx += ark_bn254::g2::Config::COEFF_B; //    30.  gx = gx + B
        let mut y = gx.sqrt().expect("to be a square"); //    31.   y = sqrt(gx)
        let e3 = Self::fq2_sgn0(u) ^ Self::fq2_sgn0(&y); // 32.  e3 = sgn0(u) == sgn0(y)
        y = Self::fq2_conditional_negate(&y, e3); //    33.   y = CMOV(-y, y, e3)       # Select correct sign of y

        Self(Bn254G2Projective::new_unchecked(x, y, Fq2::ONE))
    }
}
