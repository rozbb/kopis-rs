//! Contains the crate's arithmetic: [`plain_arith`] for ring elements and matrices in the
//! coefficient domain, [`ntt_arith`] for the NTT-domain types the rest of the crate multiplies
//! through, and [`ntt_crt`] for the two-prime transform underneath them.

pub(crate) mod ntt_arith;
pub(crate) mod ntt_crt;
mod plain_arith;

// Export all the underlying types
pub(crate) use ntt_arith::*;
pub(crate) use plain_arith::*;
