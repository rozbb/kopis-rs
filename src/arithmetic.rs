//! Contains modules for ring, matrix and NTT arithmetic

pub(crate) mod ntt_arith;
pub(crate) mod ntt_crt;
mod plain_arith;

// Export all the underlying types
pub(crate) use ntt_arith::*;
pub(crate) use plain_arith::*;
