/// The degree of the polynomial ring over Z/qZ
pub(crate) const RING_DEG: usize = 256;

// The parameters ℓ, t, and μ from the spec

pub(crate) const KOPIS512_L: usize = 2;
pub(crate) const KOPIS512_T: usize = 3;
pub(crate) const KOPIS512_MU: usize = 10;

pub(crate) const KOPIS768_L: usize = 3;
pub(crate) const KOPIS768_T: usize = 4;
pub(crate) const KOPIS768_MU: usize = 8;

pub(crate) const KOPIS1024_L: usize = 4;
pub(crate) const KOPIS1024_T: usize = 6;
pub(crate) const KOPIS1024_MU: usize = 6;

// We need to store maximum values because we can't do const arithmetic on some buffer sizes

/// The maximum possible μ value is μ=10, set by Kopis-512
pub(crate) const MAX_MU: usize = 10;

/// The maximum possible l value is l=4, set by Kopis-1024
pub(crate) const MAX_L: usize = 4;

/// The maximum possible log(T) value is T=6, set by Kopis-1024
pub(crate) const MAX_T: usize = 6;

// Domain separators for TurboSHAKE invocations
pub(crate) const DOMSEP_KGEXPAND: u8 = 0x01;
pub(crate) const DOMSEP_GENMAT: u8 = 0x02;
pub(crate) const DOMSEP_GENSEC: u8 = 0x03;
pub(crate) const DOMSEP_PKHASH: u8 = 0x04;
pub(crate) const DOMSEP_FO: u8 = 0x05;
pub(crate) const DOMSEP_NOREJECT: u8 = 0x06;
