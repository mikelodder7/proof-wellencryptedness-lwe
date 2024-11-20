use bellman::*;
use blsful::inner_types::*;

/// A gadget for a 16-bit value add, multiply, and range operations
#[derive(Debug, Clone, Copy)]
pub struct Gadget16Bit {
    lhs: Option<u16>,
    rhs: Option<u16>,
}

impl Gadget16Bit {
    pub fn lhs(&self) -> Result<u16, SynthesisError>  {
        self.lhs.ok_or(SynthesisError::AssignmentMissing)
    }
    pub fn rhs(&self) -> Result<u16, SynthesisError> {
        self.rhs.ok_or(SynthesisError::AssignmentMissing)
    }

    pub fn add<CS: ConstraintSystem<Scalar>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let lhs = self.lhs()?;
        let rhs = self.rhs()?;
        let sum = lhs.wrapping_add(rhs);

        let lhs = cs.alloc(|| "lhs", || Ok(Scalar::from(lhs)))?;
        let rhs = cs.alloc(|| "rhs", || Ok(Scalar::from(rhs)))?;
        let sum = cs.alloc(|| "sum", || Ok(Scalar::from(sum)))?;

        cs.enforce(
            || "16-bit add",
            |lc| lc + lhs + rhs,
            |lc| lc + CS::one(),
            |lc| lc + sum,
        );

        Ok(())
    }

    pub fn mul<CS: ConstraintSystem<Scalar>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let lhs = self.lhs()?;
        let rhs = self.rhs()?;
        let product = lhs.wrapping_mul(rhs);

        let lhs = cs.alloc(|| "lhs", || Ok(Scalar::from(lhs)))?;
        let rhs = cs.alloc(|| "rhs", || Ok(Scalar::from(rhs)))?;
        let product = cs.alloc(|| "product", || Ok(Scalar::from(product)))?;

        cs.enforce(
            || "16-bit multiply",
            |lc| lc + lhs,
            |lc| lc + rhs,
            |lc| lc + product,
        );

        Ok(())
    }

    pub fn range_proof<CS: ConstraintSystem<Scalar>>(
        cs: &mut CS,
        value: Option<u16>,
    ) -> Result<(), SynthesisError> {
        let value = value.ok_or(SynthesisError::AssignmentMissing)?;

        let sc_value = cs.alloc(|| "lhs", || Ok(Scalar::from(value)))?;

        let mut reconstructed = LinearCombination::zero();

        // Decompose the value into 16 bits
        for i in 0..16 {
            let j = (value >> i) & 1;

            let bit = cs.alloc(|| format!("bit {}", i), || Ok(Scalar::from(j)))?;
            // Ensure the bit is binary (0 or 1)
            cs.enforce(
                || format!("bit {} binary constraint", i),
                |lc| lc + bit,
                |lc| lc + bit,
                |lc| lc + bit,
            );

            let power = cs.alloc(|| format!("power {}", i), || Ok(Scalar::from(1u16 << i)))?;
            let term = cs.alloc(|| format!("term {}", i), || Ok(Scalar::from(j * (1 << i))))?;

            cs.enforce(
                || format!("bit {} * 2^{}", i, i),
                |lc| lc + power,
                |lc| lc + bit,
                |lc| lc + term,
            );

            reconstructed = reconstructed + power;
        }

        // Finally, enforce that our running sum equals the original value
        cs.enforce(
            || "range proof sum check",
            |lc| lc + &reconstructed,
            |lc| lc + CS::one(),
            |lc| lc + sc_value,
        );

        Ok(())
    }
}
