mod bn254;
use bn254::*;

use bellman::groth16::{ParameterSource, Proof, VerifyingKey};
use bellman::*;

use digest::{Digest, ExtendableOutput, ExtendableOutputReset, Update};
use elliptic_curve::group::Curve;
use elliptic_curve_tools::SumOfProducts;
use frodo_kem_rs::hazmat::{
    Ciphertext, CiphertextRef, EncryptionKey, EncryptionKeyRef, Expanded, Kem, Params, Sample,
    SharedSecret,
};
use ml_kem::array::typenum::Unsigned;
use ml_kem::{kem::EncapsulationKey, EncodedSizeUser, KemCore, MlKem512, MlKem512Params};
use pairing::{Engine, MultiMillerLoop};
use rand_core::CryptoRngCore;
use std::marker::PhantomData;
use std::ops::{Index, Neg};
use elliptic_curve::PrimeField;
use zeroize::Zeroize;

// /// A gadget for a 16-bit value add, multiply, and range operations
// #[derive(Debug, Clone, Copy)]
// pub struct Uint16 {
//     value: u16,
//     variable: Variable,
//     modulus: Variable,
// }
//
// impl Uint16 {
//     pub fn new(value: u16, variable: Variable, modulus: Variable) -> Self {
//         Self {
//             value,
//             variable,
//             modulus,
//         }
//     }
//
//     pub fn value(&self) -> u16 {
//         self.value
//     }
//
//     pub fn variable(&self) -> Variable {
//         self.variable
//     }
//
//     pub fn modulus(&self) -> Variable {
//         self.modulus
//     }
//
//     pub fn add<CS: ConstraintSystem<Scalar>>(
//         &self,
//         mut cs: CS,
//         other: &Self,
//     ) -> Result<Self, SynthesisError> {
//         let lhs = self.value;
//         let rhs = other.value;
//         let sum = lhs.wrapping_add(rhs);
//         let raw_sum = (lhs as u32) + (rhs as u32);
//         let quotient = raw_sum / 65536;
//
//         let sum_var = cs.alloc(|| "sum", || Ok(Scalar::from(sum)))?;
//         let raw_sum_var = cs.alloc(|| "raw sum", || Ok(Scalar::from(raw_sum)))?;
//         let quotient_var = cs.alloc(|| "quotient sum", || Ok(Scalar::from(quotient)))?;
//
//         cs.enforce(
//             || "addition raw sum",
//             |lc| lc + self.variable + other.variable,
//             |lc| lc + CS::one(),
//             |lc| lc + raw_sum_var,
//         );
//         cs.enforce(
//             || "addition modulus",
//             |lc| lc + quotient_var,
//             |lc| lc + self.modulus,
//             |lc| lc + raw_sum_var - sum_var,
//         );
//
//         Ok(Self {
//             value: sum,
//             variable: sum_var,
//             modulus: self.modulus,
//         })
//     }
//
//     pub fn mul<CS: ConstraintSystem<Scalar>>(
//         &self,
//         mut cs: CS,
//         other: &Self,
//     ) -> Result<Self, SynthesisError> {
//         let lhs = self.value;
//         let rhs = other.value;
//         let prod = lhs.wrapping_mul(rhs);
//         let raw_prod = (lhs as u32) * (rhs as u32);
//         let quotient = raw_prod / 65536;
//
//         let prod_var = cs.alloc(|| "product input", || Ok(Scalar::from(prod)))?;
//         let raw_prod_var = cs.alloc(|| "raw product input", || Ok(Scalar::from(raw_prod)))?;
//         let quotient_var = cs.alloc(|| "quotient input", || Ok(Scalar::from(quotient)))?;
//
//         // raw_product = a * b
//         cs.enforce(
//             || "raw product",
//             |lc| lc + self.variable,
//             |lc| lc + other.variable,
//             |lc| lc + raw_prod_var,
//         );
//         // raw_product = quotient * modulus + c
//         cs.enforce(
//             || "product modulus",
//             |lc| lc + quotient_var,
//             |lc| lc + self.modulus,
//             |lc| lc + raw_prod_var - prod_var,
//         );
//         Ok(Self {
//             value: prod,
//             variable: prod_var,
//             modulus: self.modulus,
//         })
//     }
//
//     pub fn equal<CS: ConstraintSystem<Scalar>>(
//         &self,
//         mut cs: CS,
//         other: &Self,
//     ) -> Result<(), SynthesisError> {
//         cs.enforce(
//             || "equal",
//             |lc| lc + self.variable,
//             |lc| lc + CS::one(),
//             |lc| lc + other.variable,
//         );
//         Ok(())
//     }
// }
//
// /// Provides a view for a matrix if stored or just returns a default value
// #[derive(Debug, Clone, Copy)]
// struct MatrixView<'a> {
//     matrix: Option<&'a [u16]>,
//     length: usize,
// }
//
// impl<'a> Index<usize> for MatrixView<'a> {
//     type Output = u16;
//
//     fn index(&self, index: usize) -> &Self::Output {
//         self.matrix.map_or(&0, |matrix| &matrix[index])
//     }
// }
//
// impl<'a> MatrixView<'a> {
//     pub fn new(matrix: Option<&'a [u16]>, length: usize) -> Self {
//         Self { matrix, length }
//     }
//
//     pub fn len(&self) -> usize {
//         self.length
//     }
// }
//
// #[derive(Debug, Clone)]
// pub struct FrodoKemCircuitPublicKey<E: MultiMillerLoop> {
//     acc: E::G1,
//     alpha_g1_beta_g2: E::Gt,
//     neg_gamma_g2: E::G2Prepared,
//     neg_delta_g2: E::G2Prepared,
//     ic: Vec<E::G1Affine>,
// }
//
// impl FrodoKemCircuitPublicKey<Bn254> {
//     pub fn from_kem_public_key<K>(
//         public_key: &EncryptionKey<K>,
//         _kem: &K,
//         verifying_key: &VerifyingKey<Bn254>,
//     ) -> Self
//     where
//         K: Kem,
//     {
//         let inputs = EncryptionKeyRef::from(public_key)
//             .as_ref()
//             .iter()
//             .zip(verifying_key.ic.iter().skip(1)) // 1 is the constraint::ONE
//             .map(|(&i, &p)| (Scalar::from(i), G1Projective::from(p)))
//             .collect::<Vec<_>>();
//
//         println!("inputs.len() = {}", inputs.len());
//         let ic = (&verifying_key.ic[1 + inputs.len()..]).to_vec();
//
//         let acc = verifying_key.ic[0]
//             + <G1Projective as SumOfProducts>::sum_of_products(inputs.as_slice());
//
//         Self {
//             acc,
//             alpha_g1_beta_g2: Bn254::pairing(&verifying_key.alpha_g1, &verifying_key.beta_g2),
//             neg_gamma_g2: verifying_key.gamma_g2.neg().into(),
//             neg_delta_g2: verifying_key.delta_g2.neg().into(),
//             ic,
//         }
//     }
// }
//
// #[derive(Debug, Clone, Copy)]
// pub struct FrodoKemEncapsulateCircuit<'a, P: Params> {
//     /// The public key matrix a expanded
//     matrix_a: MatrixView<'a>,
//     /// The secret matrix s
//     matrix_s: MatrixView<'a>,
//     /// The public key matrix b unpacked
//     matrix_b: MatrixView<'a>,
//     /// The secret error noise matrix e'
//     matrix_ep: MatrixView<'a>,
//     /// The secret error noise matrix e''
//     matrix_epp: MatrixView<'a>,
//     /// The encrypted secret µ encoded
//     mu: MatrixView<'a>,
//     /// The ciphertext c1 unpacked
//     c1: MatrixView<'a>,
//     /// The ciphertext c2 unpacked
//     c2: MatrixView<'a>,
//     _marker: PhantomData<P>,
// }
//
// impl<'a, P: Params> Default for FrodoKemEncapsulateCircuit<'a, P> {
//     fn default() -> Self {
//         Self {
//             matrix_a: MatrixView::new(None, P::N_X_N),
//             matrix_s: MatrixView::new(None, P::N_X_N_BAR),
//             matrix_b: MatrixView::new(None, P::N_X_N_BAR),
//             matrix_ep: MatrixView::new(None, P::N_X_N_BAR),
//             matrix_epp: MatrixView::new(None, P::N_BAR_X_N_BAR),
//             c1: MatrixView::new(None, P::N_X_N_BAR),
//             c2: MatrixView::new(None, P::N_BAR_X_N_BAR),
//             mu: MatrixView::new(None, P::N_BAR_X_N_BAR),
//             _marker: PhantomData,
//         }
//     }
// }
//
// impl<'a, P: Params> Circuit<Scalar> for FrodoKemEncapsulateCircuit<'a, P> {
//     fn synthesize<CS: ConstraintSystem<Scalar>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
//         let modulus = cs.alloc_input(|| "16-bit modulus", || Ok(Scalar::from(65536u32)))?;
//
//         // allocate the public inputs
//         // seed_a expanded
//         let mut matrix_a = Vec::with_capacity(P::N_X_N);
//         // public key matrix b unpacked
//         let mut matrix_b = Vec::with_capacity(P::N_X_N_BAR);
//         // ciphertext c1 unpacked
//         let mut c1 = Vec::with_capacity(P::N_X_N_BAR);
//         // ciphertext c2 unpacked
//         let mut c2 = Vec::with_capacity(P::N_BAR_X_N_BAR);
//
//         for i in 0..self.matrix_a.len() {
//             let matrix_a_i = cs.alloc_input(
//                 || format!("matrix_a[{}]", i),
//                 || Ok(Scalar::from(self.matrix_a[i])),
//             )?;
//             matrix_a.push(Uint16 {
//                 value: self.matrix_a[i],
//                 variable: matrix_a_i,
//                 modulus,
//             });
//         }
//         for i in 0..self.matrix_b.len() {
//             let matrix_b_i = cs.alloc_input(
//                 || format!("matrix_b[{}]", i),
//                 || Ok(Scalar::from(self.matrix_b[i])),
//             )?;
//             matrix_b.push(Uint16 {
//                 value: self.matrix_b[i],
//                 variable: matrix_b_i,
//                 modulus,
//             });
//         }
//         for i in 0..self.c1.len() {
//             let c1_i = cs.alloc_input(|| format!("c1[{}]", i), || Ok(Scalar::from(self.c1[i])))?;
//             c1.push(Uint16 {
//                 value: self.c1[i],
//                 variable: c1_i,
//                 modulus,
//             });
//         }
//         for i in 0..self.c2.len() {
//             let c2_i = cs.alloc_input(|| format!("c2[{}]", i), || Ok(Scalar::from(self.c2[i])))?;
//             c2.push(Uint16 {
//                 value: self.c2[i],
//                 variable: c2_i,
//                 modulus,
//             });
//         }
//
//         // allocate the witness data
//         let mut matrix_s = Vec::with_capacity(P::N_X_N_BAR);
//         let mut matrix_ep = Vec::with_capacity(P::N_X_N_BAR);
//         let mut matrix_epp = Vec::with_capacity(P::N_BAR_X_N_BAR);
//         let mut mu = Vec::with_capacity(P::N_BAR_X_N_BAR);
//
//         for i in 0..self.matrix_s.len() {
//             let matrix_s_i = cs.alloc(
//                 || format!("matrix_s[{}]", i),
//                 || Ok(Scalar::from(self.matrix_s[i])),
//             )?;
//             matrix_s.push(Uint16 {
//                 value: self.matrix_s[i],
//                 variable: matrix_s_i,
//                 modulus,
//             });
//         }
//         for i in 0..self.matrix_ep.len() {
//             let matrix_ep_i = cs.alloc(
//                 || format!("matrix_ep[{}]", i),
//                 || Ok(Scalar::from(self.matrix_ep[i])),
//             )?;
//             matrix_ep.push(Uint16 {
//                 value: self.matrix_ep[i],
//                 variable: matrix_ep_i,
//                 modulus,
//             });
//         }
//         for i in 0..self.matrix_epp.len() {
//             let matrix_epp_i = cs.alloc(
//                 || format!("matrix_epp[{}]", i),
//                 || Ok(Scalar::from(self.matrix_epp[i])),
//             )?;
//             matrix_epp.push(Uint16 {
//                 value: self.matrix_epp[i],
//                 variable: matrix_epp_i,
//                 modulus,
//             });
//         }
//         for i in 0..self.mu.len() {
//             let mu_i = cs.alloc(|| format!("mu[{}]", i), || Ok(Scalar::from(self.mu[i])))?;
//             mu.push(Uint16 {
//                 value: self.mu[i],
//                 variable: mu_i,
//                 modulus,
//             });
//         }
//
//         self.mul_add_sa_plus_e(cs, &matrix_s, &matrix_a, &matrix_ep, &c1)?;
//         self.mul_add_sb_plus_e_plus_mu(cs, &matrix_s, &matrix_b, &matrix_epp, &mu, &c2)?;
//
//         Ok(())
//     }
// }
//
// impl<'a, P: Params> FrodoKemEncapsulateCircuit<'a, P> {
//     pub fn new(
//         matrix_a: &'a [u16],
//         matrix_s: &'a [u16],
//         matrix_b: &'a [u16],
//         matrix_ep: &'a [u16],
//         matrix_epp: &'a [u16],
//         c1: &'a [u16],
//         c2: &'a [u16],
//         mu: &'a [u16],
//     ) -> Self {
//         debug_assert_eq!(matrix_a.len(), P::N_X_N);
//         debug_assert_eq!(matrix_s.len(), P::N_X_N_BAR);
//         debug_assert_eq!(matrix_b.len(), P::N_X_N_BAR);
//         debug_assert_eq!(matrix_ep.len(), P::N_X_N_BAR);
//         debug_assert_eq!(matrix_epp.len(), P::N_BAR_X_N_BAR);
//         debug_assert_eq!(c1.len(), P::N_X_N_BAR);
//         debug_assert_eq!(c2.len(), P::N_BAR_X_N_BAR);
//         debug_assert_eq!(mu.len(), P::N_BAR_X_N_BAR);
//
//         Self {
//             matrix_a: MatrixView::new(Some(matrix_a), P::N_X_N),
//             matrix_s: MatrixView::new(Some(matrix_s), P::N_X_N_BAR),
//             matrix_b: MatrixView::new(Some(matrix_b), P::N_X_N_BAR),
//             matrix_ep: MatrixView::new(Some(matrix_ep), P::N_X_N_BAR),
//             matrix_epp: MatrixView::new(Some(matrix_epp), P::N_BAR_X_N_BAR),
//             c1: MatrixView::new(Some(c1), P::N_X_N_BAR),
//             c2: MatrixView::new(Some(c2), P::N_BAR_X_N_BAR),
//             mu: MatrixView::new(Some(mu), P::N_BAR_X_N_BAR),
//             _marker: PhantomData,
//         }
//     }
//
//     fn mul_add_sa_plus_e<CS: ConstraintSystem<Scalar>>(
//         &self,
//         cs: &mut CS,
//         s: &[Uint16],
//         a: &[Uint16],
//         e: &[Uint16],
//         c1: &[Uint16],
//     ) -> Result<(), SynthesisError> {
//         for i in 0..P::N {
//             for k in 0..P::N_BAR {
//                 let k_n = k * P::N;
//                 let mut sum = e[k_n + i];
//                 for j in 0..P::N {
//                     let prod = a[j * P::N + i].mul(
//                         cs.namespace(|| format!("s*a[{}][{}][{}]", i, k, j)),
//                         &s[k_n + j],
//                     )?;
//                     sum = sum.add(
//                         cs.namespace(|| format!("s*a+e[{}][{}][{}]", i, k, j)),
//                         &prod,
//                     )?;
//                 }
//                 sum.equal(
//                     cs.namespace(|| format!("mul_add_sa_plus_e[{}][{}]", i, k)),
//                     &c1[k_n + i],
//                 )?;
//             }
//         }
//         Ok(())
//     }
//
//     fn mul_add_sb_plus_e_plus_mu<CS: ConstraintSystem<Scalar>>(
//         &self,
//         cs: &mut CS,
//         s: &[Uint16],
//         b: &[Uint16],
//         e: &[Uint16],
//         mu: &[Uint16],
//         c2: &[Uint16],
//     ) -> Result<(), SynthesisError> {
//         for k in 0..P::N_BAR {
//             let k_n = k * P::N;
//             let k_bar = k * P::N_BAR;
//             for i in 0..P::N_BAR {
//                 let mut sum = e[k_bar + i].add(
//                     cs.namespace(|| format!("e + mu [{}][{}]", k, i)),
//                     &mu[k_bar + i],
//                 )?;
//                 for j in 0..P::N {
//                     let prod = s[k_n + j].mul(
//                         cs.namespace(|| format!("s*b[{}][{}][{}]", k, i, j)),
//                         &b[j * P::N_BAR + i],
//                     )?;
//
//                     sum = sum.add(
//                         cs.namespace(|| format!("s*b + e + mu[{}][{}][{}]", k, i, j)),
//                         &prod,
//                     )?;
//                 }
//                 sum.equal(
//                     cs.namespace(|| format!("mul_add_sb_plus_e[{}][{}]", k, i)),
//                     &c2[k_bar + i],
//                 )?;
//             }
//         }
//         Ok(())
//     }
// }
//
// #[derive(Debug, Clone, Copy)]
// pub struct FrodoKemEncapsulateCircuit2<'a, P: Params> {
//     ct: Option<CiphertextRef<'a, P>>,
//     pk: Option<EncryptionKeyRef<'a, P>>,
// }
//
// impl<'a, P: Params> Default for FrodoKemEncapsulateCircuit2<'a, P> {
//     fn default() -> Self {
//         Self { ct: None, pk: None }
//     }
// }
//
// impl<'a, P: Params> Circuit<blsful::inner_types::Scalar> for FrodoKemEncapsulateCircuit2<'a, P> {
//     fn synthesize<CS: ConstraintSystem<blsful::inner_types::Scalar>>(
//         self,
//         cs: &mut CS,
//     ) -> Result<(), SynthesisError> {
//         let (preimage_bits, digest_bits) = match (self.pk, self.ct) {
//             (Some(pk), Some(ct)) => {
//                 println!("pk.len() = {}", pk.as_ref().len());
//                 println!("ct.len() = {}", ct.as_ref().len());
//                 let mut hasher = sha2::Sha256::default();
//                 Update::update(&mut hasher, pk.as_ref());
//                 Update::update(&mut hasher, ct.as_ref());
//                 let digest = hasher.finalize();
//
//                 (
//                     bits_to_gadgets(
//                         pk.as_ref()
//                             .iter()
//                             .chain(ct.as_ref().iter())
//                             .flat_map(|&v| (0..8).rev().map(move |i| (v >> i) & 1 == 1))
//                             .map(|b| Some(b)),
//                         cs,
//                     )?,
//                     bits_to_gadgets(
//                         digest
//                             .iter()
//                             .flat_map(|&v| (0..8).rev().map(move |i| (v >> i) & 1 == 1))
//                             .map(|b| Some(b)),
//                         cs,
//                     )?,
//                 )
//             }
//             _ => (
//                 bits_to_gadgets(
//                     std::iter::repeat_n(None, P::CIPHERTEXT_LENGTH + P::PUBLIC_KEY_LENGTH * 8),
//                     cs,
//                 )?,
//                 bits_to_gadgets(std::iter::repeat_n(None, 32 * 8), cs)?,
//             ),
//         };
//
//         println!("preimage_bits.len() = {}", preimage_bits.len());
//
//         let hash = gadgets::sha256::sha256(cs.namespace(|| "sha256d"), preimage_bits.as_slice())?;
//
//         debug_assert_eq!(hash.len(), digest_bits.len());
//
//         for (i, (a_bit, b_bit)) in hash.iter().zip(digest_bits.iter()).enumerate() {
//             gadgets::boolean::Boolean::enforce_equal(
//                 cs.namespace(|| format!("digest bit {}", i)),
//                 a_bit,
//                 b_bit,
//             )?;
//         }
//
//         gadgets::multipack::pack_into_inputs(
//             cs.namespace(|| "public key and ciphertext"),
//             &preimage_bits,
//         )?;
//
//         gadgets::multipack::pack_into_inputs(cs.namespace(|| "computed digest"), hash.as_ref())?;
//
//         Ok(())
//     }
// }
//
fn bits_to_gadgets<I, F, CS>(
    iter: I,
    cs: &mut CS,
) -> Result<Vec<gadgets::boolean::Boolean>, SynthesisError>
where
    I: Iterator<Item = Option<bool>>,
    F: PrimeField,
    CS: ConstraintSystem<F>,
{
    iter.enumerate()
        .map(|(i, b)| {
            gadgets::boolean::AllocatedBit::alloc(
                cs.namespace(|| format!("ciphertext bit {}", i)),
                b,
            )
        })
        .map(|b| b.map(gadgets::boolean::Boolean::from))
        .collect::<Result<Vec<_>, _>>()
}

// #[derive(Copy, Clone, Default, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
// pub struct FrodoKemWithZkp<P: Params, E: Expanded, S: Sample>(pub PhantomData<(P, E, S)>);
//
// impl<P: Params, E: Expanded, S: Sample> Params for FrodoKemWithZkp<P, E, S> {
//     type Shake = P::Shake;
//
//     const N: usize = P::N;
//     const LOG_Q: usize = P::LOG_Q;
//     const EXTRACTED_BITS: usize = P::EXTRACTED_BITS;
//     const CDF_TABLE: &'static [u16] = P::CDF_TABLE;
//     const CLAIMED_NIST_LEVEL: usize = P::CLAIMED_NIST_LEVEL;
//     const SHARED_SECRET_LENGTH: usize = P::SHARED_SECRET_LENGTH;
//     const BYTES_SEED_SE: usize = P::BYTES_SEED_SE;
//     const BYTES_SALT: usize = P::BYTES_SALT;
// }
//
// impl<P: Params, E: Expanded, S: Sample> Expanded for FrodoKemWithZkp<P, E, S> {
//     const METHOD: &'static str = E::METHOD;
//
//     fn expand_a(&self, seed_a: &[u8], a: &mut [u16]) {
//         E::expand_a(&E::default(), seed_a, a)
//     }
// }
//
// impl<P: Params, E: Expanded, S: Sample> Sample for FrodoKemWithZkp<P, E, S> {
//     fn sample(&self, s: &mut [u16]) {
//         S::sample(&S::default(), s)
//     }
// }
//
// impl<P: Params, E: Expanded, S: Sample> Kem for FrodoKemWithZkp<P, E, S> {
//     const NAME: &'static str = "FrodoKEM";
// }
//
// impl<P: Params, E: Expanded, S: Sample> FrodoKemWithZkp<P, E, S> {
//     pub fn encapsulate_with_zkp<'a, I, PP>(
//         &self,
//         public_key: I,
//         mu: &[u8],
//         salt: &[u8],
//         params: PP,
//         mut rng: impl CryptoRngCore,
//     ) -> (
//         Ciphertext<Self>,
//         SharedSecret<Self>,
//         Proof<blsful::inner_types::Bls12>,
//     )
//     where
//         I: Into<EncryptionKeyRef<'a, Self>>,
//         PP: ParameterSource<blsful::inner_types::Bls12>,
//     {
//         assert_eq!(mu.len(), Self::BYTES_MU);
//         assert_eq!(salt.len(), Self::BYTES_SALT);
//         let public_key = public_key.into();
//         let mut ct = Ciphertext::default();
//
//         let mut shake = P::Shake::default();
//         let mut g2_in = vec![0u8; Self::BYTES_PK_HASH + Self::BYTES_MU + Self::BYTES_SALT];
//
//         shake.update(public_key.seed_a());
//         shake.finalize_xof_reset_into(&mut g2_in[..Self::BYTES_PK_HASH]);
//         g2_in[Self::BYTES_PK_HASH..Self::BYTES_PK_HASH + Self::BYTES_MU].copy_from_slice(mu);
//         g2_in[Self::BYTES_PK_HASH + Self::BYTES_MU..].copy_from_slice(salt);
//         let mut g2_out = vec![0u8; Self::SHARED_SECRET_LENGTH + Self::BYTES_SEED_SE];
//         shake.update(&g2_in);
//         shake.finalize_xof_reset_into(&mut g2_out);
//
//         let mut sp = vec![0u16; (2 * Self::N + Self::N_BAR) * Self::N_BAR];
//         shake.update(&[0x96]);
//         shake.update(&g2_out[..Self::BYTES_SEED_SE]);
//         {
//             let bytes_sp =
//                 unsafe { std::slice::from_raw_parts_mut(sp.as_mut_ptr() as *mut u8, sp.len() * 2) };
//             shake.finalize_xof_reset_into(bytes_sp);
//         }
//         #[cfg(target_endian = "big")]
//         {
//             for b in sp.iter_mut() {
//                 *b = b.to_be();
//             }
//         }
//
//         self.sample(&mut sp);
//
//         let s = &sp[..Self::N_X_N_BAR];
//         let ep = &sp[Self::N_X_N_BAR..2 * Self::N_X_N_BAR];
//         let epp = &sp[2 * Self::N_X_N_BAR..];
//
//         let mut matrix_a = vec![0u16; Self::N_X_N];
//         self.expand_a(public_key.seed_a(), &mut matrix_a);
//
//         let mut matrix_b = vec![0u16; Self::N_X_N_BAR];
//         self.mul_add_sa_plus_e(s, &matrix_a, ep, &mut matrix_b);
//
//         self.pack(&matrix_b, ct.c1_mut());
//
//         let mut pk_matrix_b = vec![0u16; Self::N_X_N_BAR];
//         self.unpack(public_key.matrix_b(), &mut pk_matrix_b);
//
//         let mut matrix_v = vec![0u16; Self::N_BAR_X_N_BAR];
//         self.mul_add_sb_plus_e(s, &pk_matrix_b, epp, &mut matrix_v);
//
//         let mut matrix_c = vec![0u16; Self::N_BAR_X_N_BAR];
//
//         self.encode_message(
//             &g2_in[Self::BYTES_PK_HASH..Self::BYTES_PK_HASH + Self::BYTES_MU],
//             &mut matrix_c,
//         );
//         let mut mu_encoded = vec![0u16; Self::N_BAR_X_N_BAR];
//         mu_encoded.copy_from_slice(&matrix_c[..]);
//
//         self.add(&matrix_v, &mut matrix_c);
//
//         self.pack(&matrix_c, ct.c2_mut());
//
//         ct.salt_mut()
//             .copy_from_slice(&g2_in[g2_in.len() - Self::BYTES_SALT..]);
//
//         shake.update(ct.as_ref());
//         shake.update(&g2_out[Self::BYTES_SEED_SE..]);
//         let ss = SharedSecret::try_from(shake.finalize_boxed(P::SHARED_SECRET_LENGTH)).unwrap();
//
//         let circuit = FrodoKemEncapsulateCircuit2::<Self> {
//             ct: Some(CiphertextRef::from(&ct)),
//             pk: Some(public_key),
//         };
//
//         let before = std::time::Instant::now();
//         let proof = groth16::create_random_proof(circuit, params, &mut rng).unwrap();
//         println!("Time to create proof: {:?}", before.elapsed());
//
//         matrix_v.zeroize();
//         sp.zeroize();
//         g2_in[Self::BYTES_PK_HASH..].zeroize();
//         g2_out.zeroize();
//         mu_encoded.zeroize();
//
//         (ct, ss, proof)
//     }
//
//     pub fn verify_encapsulated_correctness<'a, C>(
//         &self,
//         public_key: &FrodoKemCircuitPublicKey<Bn254>,
//         ciphertext: C,
//         proof: &Proof<Bn254>,
//     ) -> Result<(), String>
//     where
//         C: Into<CiphertextRef<'a, Self>>,
//     {
//         let ciphertext = ciphertext.into();
//
//         let mut matrix_c1 = vec![0u16; Self::N_X_N_BAR];
//         self.unpack(ciphertext.c1(), &mut matrix_c1);
//         let mut matrix_c2 = vec![0u16; Self::N_BAR_X_N_BAR];
//         self.unpack(ciphertext.c2(), &mut matrix_c2);
//
//         let inputs = matrix_c1
//             .iter()
//             .chain(matrix_c2.iter())
//             .zip(public_key.ic.iter())
//             .map(|(i, p)| (Scalar::from(*i), G1Projective::from(*p)))
//             .collect::<Vec<_>>();
//
//         let before = std::time::Instant::now();
//         let acc =
//             public_key.acc + <G1Projective as SumOfProducts>::sum_of_products(inputs.as_slice());
//         let res = if public_key.alpha_g1_beta_g2
//             == multi_miller_loop(&[
//                 (&proof.a, &proof.b.into()),
//                 (&acc.to_affine(), &public_key.neg_gamma_g2),
//                 (&proof.c, &public_key.neg_delta_g2),
//             ])
//             .final_exponentiation()
//         {
//             Ok(())
//         } else {
//             Err("invalid proof".to_string())
//         };
//         println!("Time to verify proof: {:?}", before.elapsed());
//         res
//     }
// }
//
pub struct KyberCircuit<F: PrimeField> {
    pk: Option<EncapsulationKey<MlKem512Params>>,
    ct: Option<ml_kem::Ciphertext<MlKem512>>,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Default for KyberCircuit<F> {
    fn default() -> Self {
        Self { pk: None, ct: None, _marker: PhantomData }
    }
}

impl<F: PrimeField> Circuit<F> for KyberCircuit<F> {
    fn synthesize<CS: ConstraintSystem<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let preimage_bits= match (self.pk, self.ct) {
            (Some(pk), Some(ct)) => {
                bits_to_gadgets(
                    pk.as_bytes()
                        .iter()
                        .chain(ct.iter())
                        .flat_map(|&v| (0..8).map(move |i| (v >> i) & 1 == 1))
                        .map(|b| Some(b)),
                    cs,
                )?
            },
            _ => bits_to_gadgets(
                std::iter::repeat_n(None, (
                    <MlKem512 as KemCore>::CiphertextSize::to_usize() +
                    <<MlKem512 as KemCore>::EncapsulationKey as EncodedSizeUser>::EncodedSize::to_usize()) * 8),
                cs,
            )?
        };

        println!("preimage_bits.len() = {}", preimage_bits.len());

        let hash = gadgets::sha256::sha256(cs.namespace(|| "sha256d"), preimage_bits.as_slice())?;

        // for (i, (a_bit, b_bit)) in hash.iter().zip(digest_bits.iter()).enumerate() {
        //     gadgets::boolean::Boolean::enforce_equal(
        //         cs.namespace(|| format!("digest bit {}", i)),
        //         a_bit,
        //         b_bit,
        //     )?;
        // }

        // preimage_bits.append(&mut digest_bits);

        gadgets::multipack::pack_into_inputs(
            cs.namespace(|| "public key, ciphertext"),
            &preimage_bits,
        )?;

        // gadgets::multipack::pack_into_inputs(
        //     cs.namespace(|| "computed digest"),
        //     &hash,
        // )?;
        //
        Ok(())
    }
}

// #[derive(Debug, Clone)]
// pub struct KyberCircuitPublicKey<E: MultiMillerLoop> {
//     acc: E::G1,
//     alpha_g1_beta_g2: E::Gt,
//     neg_gamma_g2: E::G2Prepared,
//     neg_delta_g2: E::G2Prepared,
//     ic: Vec<E::G1Affine>,
// }
//
// impl KyberCircuitPublicKey<Bn254> {
//     pub fn from_kem_public_key(
//         public_key: &EncapsulationKey<MlKem512Params>,
//         verifying_key: &VerifyingKey<Bn254>,
//     ) -> Self {
//         let inputs = public_key
//             .as_bytes()
//             .iter()
//             .zip(verifying_key.ic.iter().skip(1)) // 1 is the constraint::ONE
//             .map(|(&i, &p)| (Scalar::from(i), G1Projective::from(p)))
//             .collect::<Vec<_>>();
//
//         println!("inputs.len() = {}", inputs.len());
//         let ic = (&verifying_key.ic[1 + inputs.len()..]).to_vec();
//
//         let acc = verifying_key.ic[0]
//             + <G1Projective as SumOfProducts>::sum_of_products(inputs.as_slice());
//
//         Self {
//             acc,
//             alpha_g1_beta_g2: Bn254::pairing(&verifying_key.alpha_g1, &verifying_key.beta_g2),
//             neg_gamma_g2: verifying_key.gamma_g2.neg().into(),
//             neg_delta_g2: verifying_key.delta_g2.neg().into(),
//             ic,
//         }
//     }
// }
//
#[cfg(test)]
mod tests {
    use super::*;
    use bellman::groth16;
    use ml_kem::kem::Encapsulate;
    use rand_chacha::ChaCha8Rng;
    use rand_core::SeedableRng;

    #[test]
    fn test_encapsulate_gadget_bn254() {
        let mut rng = ChaCha8Rng::seed_from_u64(0u64);
        let (dk, ek) = MlKem512::generate(&mut rng);

        let before = std::time::Instant::now();
        let params = groth16::generate_random_parameters::<Bn254, _, _>(
            KyberCircuit::default(),
            &mut rng,
        )
            .unwrap();
        println!("Time to generate parameters: {:?}", before.elapsed());
        let pvk = groth16::prepare_verifying_key(&params.vk);

        // let pvk = KyberCircuitPublicKey::from_kem_public_key(&ek, &params.vk);
        let (ct, _sk) = ek.encapsulate(&mut rng).unwrap();
        let mut c = KyberCircuit::default();
        c.pk = Some(ek.clone());
        c.ct = Some(ct.clone());

        let before = std::time::Instant::now();
        let proof: Proof<Bn254> =
            groth16::create_random_proof(c, &params, &mut rng).unwrap();
        println!("Time to create proof: {:?}", before.elapsed());

        let mut hasher = sha2::Sha256::default();
        let ek_bytes = <EncapsulationKey<MlKem512Params> as EncodedSizeUser>::as_bytes(&ek);
        Update::update(&mut hasher, &ek_bytes);
        Update::update(&mut hasher, ct.0.as_ref());
        let digest = hasher.finalize();

        let bytes = ek_bytes
            .into_iter()
            .chain(ct.into_iter())
            .collect::<Vec<_>>();
        let bits = gadgets::multipack::bytes_to_bits_le(bytes.as_slice());
        println!("bits.len() = {}", bits.len());
        let mut inputs = gadgets::multipack::compute_multipacking(&bits);

        // let bits = gadgets::multipack::bytes_to_bits_le(digest.as_slice());
        // inputs.append(&mut gadgets::multipack::compute_multipacking(&bits));

        println!("expected inputs.len() = {}", &params.vk.ic.len());
        println!("inputs.len() = {}", inputs.len());

        let res = groth16::verify_proof(&pvk, &proof, &inputs);
        println!("{:?}", res);
    }

    #[test]
    fn test_encapsulate_gadget_bls12381() {
        let mut rng = ChaCha8Rng::seed_from_u64(0u64);
        let (dk, ek) = MlKem512::generate(&mut rng);

        let before = std::time::Instant::now();
        let params = groth16::generate_random_parameters::<blsful::inner_types::Bls12, _, _>(
            KyberCircuit::default(),
            &mut rng,
        )
        .unwrap();
        println!("Time to generate parameters: {:?}", before.elapsed());
        let pvk = groth16::prepare_verifying_key(&params.vk);

        // let pvk = KyberCircuitPublicKey::from_kem_public_key(&ek, &params.vk);
        let (ct, _sk) = ek.encapsulate(&mut rng).unwrap();
        let mut c = KyberCircuit::<blsful::inner_types::Scalar>::default();
        c.pk = Some(ek.clone());
        c.ct = Some(ct.clone());

        let before = std::time::Instant::now();
        let proof: Proof<blsful::inner_types::Bls12> =
            groth16::create_random_proof(c, &params, &mut rng).unwrap();
        println!("Time to create proof: {:?}", before.elapsed());

        let mut hasher = sha2::Sha256::default();
        let ek_bytes = <EncapsulationKey<MlKem512Params> as EncodedSizeUser>::as_bytes(&ek);
        Update::update(&mut hasher, &ek_bytes);
        Update::update(&mut hasher, ct.0.as_ref());
        let digest = hasher.finalize();

        let bytes = ek_bytes
            .into_iter()
            .chain(ct.into_iter())
            .collect::<Vec<_>>();
        let bits = gadgets::multipack::bytes_to_bits_le(bytes.as_slice());
        println!("bits.len() = {}", bits.len());
        let mut inputs = gadgets::multipack::compute_multipacking(&bits);

        // let bits = gadgets::multipack::bytes_to_bits_le(digest.as_slice());
        // inputs.append(&mut gadgets::multipack::compute_multipacking(&bits));

        println!("expected inputs.len() = {}", &params.vk.ic.len());
        println!("inputs.len() = {}", inputs.len());

        let res = groth16::verify_proof(&pvk, &proof, &inputs);
        println!("{:?}", res);
    }
}
