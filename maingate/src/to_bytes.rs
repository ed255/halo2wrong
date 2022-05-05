//! TODO

use super::main_gate::{MainGate, MainGateColumn, MainGateConfig};
use crate::halo2::arithmetic::FieldExt;
use crate::halo2::circuit::Chip;
use crate::halo2::circuit::Layouter;
use crate::halo2::plonk::{ConstraintSystem, Error};
use crate::halo2::plonk::{Selector, TableColumn};
use crate::halo2::poly::Rotation;
use crate::instructions::{CombinationOptionCommon, MainGateInstructions, Term};
use crate::{AssignedValue, UnassignedValue};
use halo2wrong::RegionCtx;
use std::cmp;
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct ToBytesConfig {
    main_gate_config: MainGateConfig,
    s_dense_limb_range: Selector,
    byte_range_table: TableColumn,
}

pub struct ToBytesChip<F: FieldExt> {
    config: ToBytesConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> ToBytesChip<F> {
    pub fn new(config: ToBytesConfig) -> Self {
        Self {
            config,
            _marker: PhantomData {},
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        main_gate_config: &MainGateConfig,
    ) -> ToBytesConfig {
        todo!();
    }

    fn base<const NUM_BYTES: usize>() -> [F; NUM_BYTES] {
        assert!(NUM_BYTES > 0);
        assert!(NUM_BYTES < 32);
        let mut base = [F::from(0); NUM_BYTES];
        for (i, b) in base.iter_mut().enumerate() {
            *b = F::from(256).pow(&[i as u64, 0, 0, 0]);
        }
        base
    }

    fn main_gate_config(&self) -> MainGateConfig {
        self.config.main_gate_config.clone()
    }

    fn main_gate(&self) -> MainGate<F> {
        MainGate::<F>::new(self.main_gate_config())
    }

    // acc = acc + sum { from i = index to index + 4 } base[i] * bytes[i]
    fn calc_acc(acc: Option<F>, bytes: &Option<Vec<F>>, index: usize, base: &[F]) -> Option<F> {
        match (acc, bytes.as_ref()) {
            (Some(acc), Some(bytes)) => Some(
                (index..index + 4)
                    .map(|i| base[i] * bytes[i])
                    .fold(acc, |accum, x| accum + x),
            ),
            _ => None,
        }
    }
}

impl<F: FieldExt> Chip<F> for ToBytesChip<F> {
    type Config = ToBytesConfig;
    type Loaded = ();
    fn config(&self) -> &Self::Config {
        &self.config
    }
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

pub trait ToBytesInstructions<F: FieldExt>: Chip<F> {
    fn to_bytes<const NUM_BYTES: usize>(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        input: &AssignedValue<F>,
    ) -> Result<[AssignedValue<F>; NUM_BYTES], Error>;

    fn load_byte_range_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error>;
}

impl<F: FieldExt> ToBytesInstructions<F> for ToBytesChip<F> {
    fn to_bytes<const NUM_BYTES: usize>(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        input: &AssignedValue<F>,
    ) -> Result<[AssignedValue<F>; NUM_BYTES], Error> {
        let main_gate = self.main_gate();
        let (one, zero) = (F::one(), F::zero());
        let base = Self::base::<NUM_BYTES>();

        let bytes: Option<Vec<F>> = input
            .value
            .map(|v| {
                let value_repr = v.to_repr();
                let bytes32 = value_repr.as_ref();
                if bytes32[NUM_BYTES..].iter().any(|&b| b != 0) {
                    // `input` doesn't fit in `NUM_BYTES`
                    return Err(Error::Synthesis);
                }
                Ok(bytes32[..NUM_BYTES]
                    .iter()
                    .map(|b| F::from(*b as u64))
                    .collect())
            })
            .transpose()?;

        let mut bytes_assigned = Vec::new();

        // A. When NUM_BYTES is between 1 and 3
        //
        // in = B^0 * b0 + B^1 * b1 + B^2 * b2
        //
        // | A        | B        | C        | D       | E        | E_next |
        // | ---      | ---      | ---      | ---     | ---      | ---    |
        // | B^0 * b0 | B^1 * b1 | B^2 * b2 | -1 * in | -        | -      |

        // B. When NUM_BYTES is between 4 and 7
        //
        // acc0 = B^0 * b0 + B^1 * b1 + B^2 * b2 + B^3 * b3
        // in   = B^4 * b4 + B^5 * b5 + B^6 * b6 + acc0
        //
        // | A        | B        | C        | D        | E        | E_next    |
        // | ---      | ---      | ---      | ---      | ---      | ---       |
        // | B^0 * b0 | B^1 * b1 | B^2 * b2 | B^3 * b3 | -        | -1 * acc0 |
        // | B^4 * b4 | B^5 * b5 | B^6 * b6 | -1 * in  | 1 * acc0 | -         |

        // B. When NUM_BYTES is between 8 and 11
        //
        // acc0 = B^0 * b0 + B^1 * b1 + B^2 * b2 + B^3 * b3
        // acc1 = B^4 * b4 + B^5 * b5 + B^6 * b6 + B^7 * b7 + acc0
        // in   = B^8 * b8 + B^9 * b9 + B^10 * b10 + acc1
        //
        // | A        | B        | C          | D        | E        | E_next    |
        // | ---      | ---      | ---        | ---      | ---      | ---       |
        // | B^0 * b0 | B^1 * b1 | B^2 * b2   | B^3 * b3 | -        | -1 * acc0 |
        // | B^4 * b4 | B^5 * b5 | B^6 * b6   | B^7 * b7 | 1 * acc0 | -1 * acc1 |
        // | B^8 * b8 | B^9 * b9 | B^10 * b10 | -1 * in  | 1 * acc1 | -         |

        let byte_terms: Vec<Term<F>> = (0..NUM_BYTES)
            .map(|i| Term::Unassigned(bytes.as_ref().map(|bytes| bytes[i]), base[i]))
            .collect();
        if byte_terms.len() <= 3 {
            // A. Single row case

            // in = B^0 * b0 + B^1 * b1 + B^2 * b2
            let term_0 = byte_terms[0].clone();
            let term_1 = byte_terms.get(1).cloned().unwrap_or(Term::Zero);
            let term_2 = byte_terms.get(2).cloned().unwrap_or(Term::Zero);
            let term_3 = Term::Assigned(*input, -F::one());
            let assigned = main_gate.combine(
                ctx,
                &[term_0, term_1, term_2, term_3, Term::Zero],
                zero,
                CombinationOptionCommon::OneLinerAdd.into(),
            )?;
            bytes_assigned.extend_from_slice(&assigned[..3]);
        } else {
            // B. Multiple row case
            let mut index = 0;

            // First row
            // acc0 = B^0 * b0 + B^1 * b1 + B^2 * b2 + B^3 * b3
            let assigned = main_gate.combine(
                ctx,
                &[
                    byte_terms[0].clone(),
                    byte_terms[1].clone(),
                    byte_terms[2].clone(),
                    byte_terms[3].clone(),
                    Term::Zero,
                ],
                zero,
                CombinationOptionCommon::CombineToNextAdd(-one).into(),
            )?;
            bytes_assigned.extend_from_slice(&assigned[..4]);
            let mut acc = bytes.as_ref().map(|_| F::zero());
            acc = Self::calc_acc(acc, &bytes, index, &base);
            index += 4;

            // Intermediate rows
            // acc1 = B^4 * b4 + B^5 * b5 + B^6 * b6 + B^7 * b7 + acc0
            while index + 3 <= NUM_BYTES {
                let assigned = main_gate.combine(
                    ctx,
                    &[
                        byte_terms[index + 0].clone(),
                        byte_terms[index + 1].clone(),
                        byte_terms[index + 2].clone(),
                        byte_terms[index + 3].clone(),
                        Term::Unassigned(acc, F::one()),
                    ],
                    zero,
                    CombinationOptionCommon::CombineToNextAdd(-one).into(),
                )?;
                bytes_assigned.extend_from_slice(&assigned[..4]);
                acc = Self::calc_acc(acc, &bytes, index, &base);
                index += 4;
            }

            // Last row
            // in   = B^8 * b8 + B^9 * b9 + B^10 * b10 + acc1
            let term_0 = byte_terms[index + 0].clone();
            let term_1 = byte_terms.get(index + 1).cloned().unwrap_or(Term::Zero);
            let term_2 = byte_terms.get(index + 2).cloned().unwrap_or(Term::Zero);
            let term_3 = Term::Assigned(*input, -F::one());
            let term_4 = Term::Unassigned(acc, F::one());

            let assigned = main_gate.combine(
                ctx,
                &[term_0, term_1, term_2, term_3, term_4],
                zero,
                CombinationOptionCommon::OneLinerAdd.into(),
            )?;
            bytes_assigned.extend_from_slice(&assigned[..4]);
        }

        Ok(bytes_assigned
            .try_into()
            .expect("bytes_assigned has unexpected size"))
    }

    fn load_byte_range_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "byte range",
            |mut table| {
                for (index, value) in (0..256).enumerate() {
                    table.assign_cell(
                        || "limb range table",
                        self.config.byte_range_table,
                        index,
                        || Ok(F::from(value)),
                    )?;
                }
                Ok(())
            },
        )?;
        Ok(())
    }
}
