use ark_bn254::Fr;
use ark_ff::{AdditiveGroup, BigInt, Field as ArkField, PrimeField as ArkPrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use blsful::vsss_rs::subtle::{Choice, CtOption};
use elliptic_curve::{Field, PrimeField};
use rand_core::RngCore;
use std::{
    borrow::Borrow,
    fmt::{self, Display, Formatter, LowerHex, UpperHex},
    iter::{Product, Sum},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use subtle::{ConditionallySelectable, ConstantTimeEq};

#[derive(Debug, Copy, Clone, Default)]
pub struct Scalar(pub Fr);

impl From<Fr> for Scalar {
    fn from(scalar: Fr) -> Self {
        Self(scalar)
    }
}

impl From<&Fr> for Scalar {
    fn from(scalar: &Fr) -> Self {
        Self(*scalar)
    }
}

impl From<Scalar> for Fr {
    fn from(value: Scalar) -> Self {
        value.0
    }
}

impl From<&Scalar> for Fr {
    fn from(value: &Scalar) -> Self {
        value.0
    }
}

impl Display for Scalar {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:x}", self)
    }
}

impl LowerHex for Scalar {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let limbs = self.0.into_bigint().0;
        for l in &limbs {
            write!(f, "{:x}", *l)?;
        }
        Ok(())
    }
}

impl UpperHex for Scalar {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let limbs = self.0.into_bigint().0;
        for l in &limbs {
            write!(f, "{:X}", *l)?;
        }
        Ok(())
    }
}

impl From<u8> for Scalar {
    fn from(value: u8) -> Self {
        Self(Fr::from(value))
    }
}

impl From<u16> for Scalar {
    fn from(value: u16) -> Self {
        Self(Fr::from(value))
    }
}

impl From<u32> for Scalar {
    fn from(value: u32) -> Self {
        Self(Fr::from(value))
    }
}

impl From<u64> for Scalar {
    fn from(value: u64) -> Self {
        Self(Fr::from(value))
    }
}

impl From<u128> for Scalar {
    fn from(value: u128) -> Self {
        Self(Fr::from(value))
    }
}

impl AsRef<Scalar> for Scalar {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl ConstantTimeEq for Scalar {
    fn ct_eq(&self, other: &Self) -> Choice {
        let lhs = self.0.into_bigint().0;
        let rhs = other.0.into_bigint().0;
        let mut res = Choice::from(1u8);
        for i in 0..4 {
            res &= lhs[i].ct_eq(&rhs[i]);
        }
        res
    }
}

impl ConditionallySelectable for Scalar {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        let mut res = [0u64; 4];
        let a = a.0.into_bigint().0;
        let b = b.0.into_bigint().0;
        for i in 0..4 {
            res[i] = u64::conditional_select(&a[i], &b[i], choice);
        }
        Self(Fr::from(BigInt::new(res)))
    }
}

impl Eq for Scalar {}

impl PartialEq for Scalar {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl Ord for Scalar {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialOrd for Scalar {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Neg for Scalar {
    type Output = Self;

    fn neg(self) -> Self::Output {
        -&self
    }
}

impl Neg for &Scalar {
    type Output = Scalar;

    fn neg(self) -> Self::Output {
        Scalar(-self.0)
    }
}

impl AddAssign for Scalar {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

ops_impl!(Add, add, +, AddAssign, add_assign, +=, LHS = Scalar, RHS = Scalar, OUTPUT = Scalar);

impl SubAssign for Scalar {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
    }
}

ops_impl!(Sub, sub, -, SubAssign, sub_assign, -=, LHS = Scalar, RHS = Scalar, OUTPUT = Scalar);

impl MulAssign for Scalar {
    fn mul_assign(&mut self, rhs: Self) {
        self.0 *= rhs.0;
    }
}

ops_impl!(Mul, mul, *, MulAssign, mul_assign, *=, LHS = Scalar, RHS = Scalar, OUTPUT = Scalar);

impl DivAssign for Scalar {
    fn div_assign(&mut self, rhs: Self) {
        self.0 *= rhs.0.inverse().expect("inverse to work");
    }
}

ops_impl!(Div, div, /, DivAssign, div_assign, /=, LHS = Scalar, RHS = Scalar, OUTPUT = Scalar);

impl<T: Borrow<Scalar>> Sum<T> for Scalar {
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        let mut sum = Fr::ZERO;
        for item in iter {
            sum += item.borrow().0;
        }
        Self(sum)
    }
}

impl<T: Borrow<Scalar>> Product<T> for Scalar {
    fn product<I: Iterator<Item = T>>(iter: I) -> Self {
        let mut product = Fr::ONE;
        for item in iter {
            product *= item.borrow().0;
        }
        Self(product)
    }
}

impl Field for Scalar {
    const ZERO: Self = Self(Fr::ZERO);
    const ONE: Self = Self(Fr::ONE);

    fn random(mut rng: impl RngCore) -> Self {
        let mut bytes = [0u8; 32];
        rng.fill_bytes(&mut bytes);
        Fr::from_random_bytes(&bytes)
            .expect("invalid randomness")
            .into()
    }

    fn square(&self) -> Self {
        self.0.square().into()
    }

    fn double(&self) -> Self {
        self.0.double().into()
    }

    fn invert(&self) -> CtOption<Self> {
        if let Some(inv) = self.0.inverse() {
            CtOption::new(inv.into(), Choice::from(1u8))
        } else {
            CtOption::new(Self::ZERO, Choice::from(0u8))
        }
    }

    fn sqrt_ratio(_num: &Self, _div: &Self) -> (Choice, Self) {
        unimplemented!()
    }

    fn sqrt_alt(&self) -> (Choice, Self) {
        unimplemented!()
    }

    fn sqrt(&self) -> CtOption<Self> {
        if let Some(sqrt) = self.0.sqrt() {
            CtOption::new(sqrt.into(), Choice::from(1u8))
        } else {
            CtOption::new(Self::ZERO, Choice::from(0u8))
        }
    }
}

impl PrimeField for Scalar {
    type Repr = [u8; 32];

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        match Fr::deserialize_compressed(&repr[..]) {
            Ok(scalar) => CtOption::new(scalar.into(), Choice::from(1u8)),
            Err(_) => CtOption::new(Self::ZERO, Choice::from(0u8)),
        }
    }

    fn to_repr(&self) -> Self::Repr {
        let mut repr = Vec::new();
        Fr::from(self)
            .serialize_compressed(&mut repr)
            .expect("serialization to work");
        repr.try_into().expect("size to match")
    }

    fn is_odd(&self) -> Choice {
        Choice::from((self.0.into_bigint().0[0] & 1) as u8)
    }

    const MODULUS: &'static str =
        "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001";
    const NUM_BITS: u32 = 254;
    const CAPACITY: u32 = Self::NUM_BITS - 1;
    const TWO_INV: Self = Self::from_be_bytes_unchecked(&hex_literal::hex!(
        "10c441f29d0c5e3f9c3f539a6a7f52936a9d23257fc15e6f74fd1a274edbcea1"
    ));
    const MULTIPLICATIVE_GENERATOR: Self = Self::from_be_bytes_unchecked(&hex_literal::hex!(
        "15d0085520f5bbc347d8eb76d8dd0689eaba68a3a32a913f1b0d0ef99fffffe6"
    ));
    const S: u32 = 28;
    const ROOT_OF_UNITY: Self = Self::from_be_bytes_unchecked(&hex_literal::hex!(
        "1cdb5c39ff3b56c597ba56981c3f8af123cfd46efb164118423f59db933a6b4c"
    ));
    const ROOT_OF_UNITY_INV: Self = Self::from_be_bytes_unchecked(&hex_literal::hex!(
        "0f78afc5f9a9e41c6f2f4de7faed5d2bf49c1203da7f40b8860c7b9b81b9b53b"
    ));
    const DELTA: Self = Self::from_be_bytes_unchecked(&hex_literal::hex!(
        "2c3f4b0d4dd837e7799b6d1e4da4c8e60a80a53ab530fda6e6809dffb040e6e9"
    ));
}

bytes_impl!(Scalar, |s: &Scalar| s.to_repr(), Scalar::from_bytes);

serde_impl!(
    Scalar,
    |s: &Scalar| s.to_repr(),
    |bytes: &[u8; Scalar::BYTES]| {
        Option::<Scalar>::from(Scalar::from_repr(*bytes)).ok_or(serdect::serde::de::Error::custom(
            "failed to deserialize scalar",
        ))
    },
    Scalar::BYTES
);

impl Scalar {
    pub const BYTES: usize = 32;

    pub const fn from_be_bytes_unchecked(bytes: &[u8; 32]) -> Self {
        Self(Fr::new_unchecked(BigInt::new([
            u64::from_be_bytes([
                bytes[24], bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30],
                bytes[31],
            ]),
            u64::from_be_bytes([
                bytes[16], bytes[17], bytes[18], bytes[19], bytes[20], bytes[21], bytes[22],
                bytes[23],
            ]),
            u64::from_be_bytes([
                bytes[8], bytes[9], bytes[10], bytes[11], bytes[12], bytes[13], bytes[14],
                bytes[15],
            ]),
            u64::from_be_bytes([
                bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
            ]),
        ])))
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() != 32 {
            return Err(format!("expected 32 bytes, got {}", bytes.len()));
        }
        let bytes = bytes
            .try_into()
            .map_err(|_| "failed to convert to array".to_string())?;
        Option::<Self>::from(Self::from_repr(bytes)).ok_or("invalid bytes".to_string())
    }
}
