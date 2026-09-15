//! This file defines and implements Kopis ring elements, specifically ℤ[X]/(X^256 + 1) mod n where
//! n can be any power of two at most 2^16

use crate::{
    consts::RING_DEG,
    ser::{deserialize_generic, serialize_10, serialize_generic},
};

use core::ops::Sub;

use zeroize::Zeroize;

/// An element of the ring (Z/2^13 Z)[X] / (X^256 + 1)
// The coefficients are in order of ascending powers, i.e., `self.0[0]` is the constant term
#[derive(Eq, PartialEq, Debug, Clone, Copy, Zeroize)]
pub struct RingElem(pub(crate) [u16; RING_DEG]);

impl Default for RingElem {
    fn default() -> Self {
        RingElem([0u16; RING_DEG])
    }
}

impl RingElem {
    /// Creates a random ring element
    #[cfg(test)]
    pub(crate) fn rand(rng: &mut impl rand_core::CryptoRng) -> Self {
        let modulus = 1u32 << 13;

        let mut result = [0; RING_DEG];
        result.iter_mut().for_each(|coeff| {
            let w = rng.next_u32() % modulus;
            *coeff = w as u16;
        });

        RingElem(result)
    }

    /// Deserializes a ring element, treating each coefficient as having only `bits_per_elem` bits.
    #[allow(clippy::unwrap_used)]
    pub(crate) fn deserialize<const BITS_PER_ELEM: usize>(bytes: &[u8]) -> Self {
        // We support deserialization of any number of bits up to 13
        debug_assert!((1..=13).contains(&BITS_PER_ELEM));
        // The bytes must be exactly RING_DEG-many copies of BITS_PER_ELEM
        assert_eq!(bytes.len(), BITS_PER_ELEM * RING_DEG / 8);

        // One AVX2 unpacker covers every width, so it subsumes both specializations below.
        #[cfg(kopis_avx2)]
        #[allow(unsafe_code)]
        if crate::backend::avx2_available() {
            // SAFETY: `avx2_available()` has just confirmed this CPU supports AVX2. The width
            // and length preconditions are the range check above and the assertion.
            return RingElem(unsafe {
                crate::backend::avx2::ser::deserialize::<BITS_PER_ELEM>(bytes)
            });
        }

        #[cfg(kopis_neon)]
        #[allow(unsafe_code)]
        if crate::backend::neon_available() {
            // SAFETY: `neon_available()` has just confirmed this CPU supports NEON. The width
            // and length preconditions are the range check above and the assertion.
            return RingElem(unsafe {
                crate::backend::neon::ser::deserialize::<BITS_PER_ELEM>(bytes)
            });
        }

        // Specialize based on bits_per_elem. unwraps are okay because of the check above
        match BITS_PER_ELEM {
            13 => {
                let arr: &[u8; 13 * RING_DEG / 8] = bytes.try_into().unwrap();
                RingElem(crate::ser::deserialize_13(arr))
            }
            10 => {
                let arr: &[u8; 10 * RING_DEG / 8] = bytes.try_into().unwrap();
                RingElem(crate::ser::deserialize_10(arr))
            }
            _ => RingElem(deserialize_generic::<RING_DEG, BITS_PER_ELEM>(bytes)),
        }
    }

    /// Serializes this ring element, treating each coefficient as having only `BITS_PER_ELEM`
    /// bits. In Saber terms, this runs POLYk2BS where k = BITS_PER_ELEM
    #[allow(clippy::unwrap_used)]
    pub(crate) fn serialize<const BITS_PER_ELEM: usize>(&self, out_buf: &mut [u8]) {
        // We support serialization of any number of bits up to 13
        debug_assert!((1..=13).contains(&BITS_PER_ELEM));
        // The output must be exactly RING_DEG-many copies of BITS_PER_ELEM
        assert_eq!(out_buf.len(), BITS_PER_ELEM * RING_DEG / 8);

        // Specialize based on BITS_PER_ELEM. unwrap is okay because of the check above
        match BITS_PER_ELEM {
            10 => {
                let arr: &mut [u8; 10 * RING_DEG / 8] = out_buf.try_into().unwrap();
                serialize_10(&self.0, arr)
            }
            _ => serialize_generic::<BITS_PER_ELEM>(&self.0, out_buf),
        }
    }

    // Algorithm 8, ShiftRight
    /// Right-shifts each coefficient by the specified amount, essentially dividing each coeff by a
    /// power of two with rounding
    pub(crate) fn shift_right(&mut self, shift: usize) {
        for coeff in self.0.iter_mut() {
            *coeff >>= shift;
        }
    }

    // Algorithm 7, ShiftLeft
    /// Left-shifts each coefficient by the specified amount, essentially multiplying each coeff by
    /// a power of two, mod 2^16
    pub(crate) fn shift_left(&mut self, shift: usize) {
        for coeff in self.0.iter_mut() {
            *coeff <<= shift;
        }
    }

    /// Adds a given value to all coefficients
    pub(crate) fn wrapping_add_to_all(&mut self, val: u16) {
        for coeff in self.0.iter_mut() {
            *coeff = coeff.wrapping_add(val);
        }
    }
}

impl<'a> Sub for &'a RingElem {
    type Output = RingElem;

    fn sub(self, other: &'a RingElem) -> Self::Output {
        let mut ret = RingElem::default();
        for i in 0..RING_DEG {
            ret.0[i] = self.0[i].wrapping_sub(other.0[i]);
        }
        ret
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::consts::RING_DEG;

    use rand::{Rng, RngCore, rng};

    // Tests serialization and deserialization of ring elements
    #[test]
    fn deserialize() {
        let mut rng = rng();

        // The largest buffer we'll need for the following tests. We make 2 because we need to
        // compare values in some places
        let mut backing_buf1 = [0u8; 16 * RING_DEG / 8];
        let mut backing_buf2 = [0u8; 16 * RING_DEG / 8];

        for _ in 0..1000 {
            // Check that deserialize matches the reference impl deserialize for N=2^13,2^10,2^1
            let bits_per_elem = 13;
            let bytes = &mut backing_buf1[..bits_per_elem * RING_DEG / 8];
            rng.fill_bytes(bytes);
            assert_eq!(
                saber_ref_from_bytes_mod8192(&bytes),
                RingElem::deserialize::<13>(&bytes)
            );

            // Now check it matches the reference to_bytes impl
            let elem = RingElem::rand(&mut rng);
            let my_bytes = &mut backing_buf1[..bits_per_elem * RING_DEG / 8];
            let ref_bytes = &mut backing_buf2[..bits_per_elem * RING_DEG / 8];
            elem.serialize::<13>(my_bytes);
            reference_impl_to_bytes_mod8192(&elem, ref_bytes);
            assert_eq!(my_bytes, ref_bytes);

            let bits_per_elem = 10;
            let bytes = &mut backing_buf1[..bits_per_elem * RING_DEG / 8];
            rng.fill_bytes(bytes);
            assert_eq!(
                saber_ref_from_bytes_mod1024(&bytes).0,
                RingElem::deserialize::<10>(&bytes).0,
            );

            let bits_per_elem = 1;
            let bytes = &mut backing_buf1[..bits_per_elem * RING_DEG / 8];
            rng.fill_bytes(bytes);
            assert_eq!(
                saber_ref_from_bytes_mod2(&bytes).0,
                RingElem::deserialize::<1>(&bytes).0,
            );

            // Now check it matches the reference to_bytes impl
            let elem = RingElem::rand(&mut rng);
            // The reference impl actually requires that the buffer is zeroed before use
            backing_buf2.fill(0);
            let my_bytes = &mut backing_buf1[..bits_per_elem * RING_DEG / 8];
            let ref_bytes = &mut backing_buf2[..bits_per_elem * RING_DEG / 8];
            elem.serialize::<1>(my_bytes);
            saber_ref_to_bytes_mod2(&elem, ref_bytes);
            assert_eq!(my_bytes, ref_bytes);

            // Now check that to_bytes and from_bytes are inverses

            // Pick a random bits_per_elem
            for _ in 0..10 {
                let bits_per_elem = rng.random_range(1..=13);
                let bitmask = (1 << bits_per_elem) - 1;

                // Generate a random element and make sure none of the values exceed 2^bits_per_elem
                let mut p = RingElem::rand(&mut rng);
                p.0.iter_mut().for_each(|e| *e &= bitmask);

                // Check that a round trip preserves the polynomial
                let p_bytes = &mut backing_buf1[..bits_per_elem * RING_DEG / 8];
                dynamic_serialize_elem(&p, p_bytes, bits_per_elem);
                assert_eq!(p, dynamic_deserialize_elem(&p_bytes, bits_per_elem));

                // Now other way around
                let p_bytes = &mut backing_buf1[..bits_per_elem * RING_DEG / 8];
                rng.fill_bytes(p_bytes);
                let p = dynamic_deserialize_elem(&p_bytes, bits_per_elem);
                let new_p_bytes = &mut backing_buf2[..bits_per_elem * RING_DEG / 8];
                dynamic_serialize_elem(&p, new_p_bytes, bits_per_elem);
                assert_eq!(p_bytes, new_p_bytes);
            }
        }

        /// Runs `elem.serialize::<bits_per_elem>(out_buf)`
        fn dynamic_serialize_elem(elem: &RingElem, out_buf: &mut [u8], bits_per_elem: usize) {
            match bits_per_elem {
                13 => elem.serialize::<13>(out_buf),
                12 => elem.serialize::<12>(out_buf),
                11 => elem.serialize::<11>(out_buf),
                10 => elem.serialize::<10>(out_buf),
                9 => elem.serialize::<9>(out_buf),
                8 => elem.serialize::<8>(out_buf),
                7 => elem.serialize::<7>(out_buf),
                6 => elem.serialize::<6>(out_buf),
                5 => elem.serialize::<5>(out_buf),
                4 => elem.serialize::<4>(out_buf),
                3 => elem.serialize::<3>(out_buf),
                2 => elem.serialize::<2>(out_buf),
                1 => elem.serialize::<1>(out_buf),
                _ => panic!("Unsupported bits_per_elem {bits_per_elem}"),
            }
        }

        /// Runs `RingElem::deserialize::<bits_per_elem>(bytes)`
        fn dynamic_deserialize_elem(bytes: &[u8], bits_per_elem: usize) -> RingElem {
            match bits_per_elem {
                13 => RingElem::deserialize::<13>(bytes),
                12 => RingElem::deserialize::<12>(bytes),
                11 => RingElem::deserialize::<11>(bytes),
                10 => RingElem::deserialize::<10>(bytes),
                9 => RingElem::deserialize::<9>(bytes),
                8 => RingElem::deserialize::<8>(bytes),
                7 => RingElem::deserialize::<7>(bytes),
                6 => RingElem::deserialize::<6>(bytes),
                5 => RingElem::deserialize::<5>(bytes),
                4 => RingElem::deserialize::<4>(bytes),
                3 => RingElem::deserialize::<3>(bytes),
                2 => RingElem::deserialize::<2>(bytes),
                1 => RingElem::deserialize::<1>(bytes),
                _ => panic!("Unsupported bits_per_elem {bits_per_elem}"),
            }
        }
    }

    /// A nearly verbatim copy of the C reference impl of BS2POL_N where N = 2^13
    /// https://github.com/KULeuven-COSIC/SABER/blob/f7f39e4db2f3e22a21e1dd635e0601caae2b4510/Reference_Implementation_KEM/pack_unpack.c#L101
    fn saber_ref_from_bytes_mod8192(b: &[u8]) -> RingElem {
        let mut offset_byte;
        let mut offset_data;
        let mut poly = RingElem::default();
        let data = &mut poly.0;

        let b_arr: [u8; 13 * RING_DEG / 8] = b.try_into().unwrap();
        let bytes = b_arr.map(|x| x as u16);

        for j in 0..RING_DEG / 8 {
            offset_byte = 13 * j;
            offset_data = 8 * j;
            data[offset_data] =
                (bytes[offset_byte] & (0xff)) | ((bytes[offset_byte + 1] & 0x1f) << 8);
            data[offset_data + 1] = (bytes[offset_byte + 1] >> 5 & (0x07))
                | ((bytes[offset_byte + 2] & 0xff) << 3)
                | ((bytes[offset_byte + 3] & 0x03) << 11);
            data[offset_data + 2] =
                (bytes[offset_byte + 3] >> 2 & (0x3f)) | ((bytes[offset_byte + 4] & 0x7f) << 6);
            data[offset_data + 3] = (bytes[offset_byte + 4] >> 7 & (0x01))
                | ((bytes[offset_byte + 5] & 0xff) << 1)
                | ((bytes[offset_byte + 6] & 0x0f) << 9);
            data[offset_data + 4] = (bytes[offset_byte + 6] >> 4 & (0x0f))
                | ((bytes[offset_byte + 7] & 0xff) << 4)
                | ((bytes[offset_byte + 8] & 0x01) << 12);
            data[offset_data + 5] =
                (bytes[offset_byte + 8] >> 1 & (0x7f)) | ((bytes[offset_byte + 9] & 0x3f) << 7);
            data[offset_data + 6] = (bytes[offset_byte + 9] >> 6 & (0x03))
                | ((bytes[offset_byte + 10] & 0xff) << 2)
                | ((bytes[offset_byte + 11] & 0x07) << 10);
            data[offset_data + 7] =
                (bytes[offset_byte + 11] >> 3 & (0x1f)) | ((bytes[offset_byte + 12] & 0xff) << 5);
        }

        poly
    }

    /// A nearly verbatim copy of the C reference impl of BS2POL_N where N = 2^10
    /// https://github.com/KULeuven-COSIC/SABER/blob/f7f39e4db2f3e22a21e1dd635e0601caae2b4510/Reference_Implementation_KEM/pack_unpack.c#L134
    fn saber_ref_from_bytes_mod1024(b: &[u8]) -> RingElem {
        let mut offset_byte;
        let mut offset_data;
        let mut poly = RingElem::default();
        let data = &mut poly.0;

        let b_arr: [u8; 10 * RING_DEG / 8] = b.try_into().unwrap();
        let bytes = b_arr.map(|x| x as u16);

        for j in 0..RING_DEG / 4 {
            offset_byte = 5 * j;
            offset_data = 4 * j;
            data[offset_data] =
                (bytes[offset_byte] & (0xff)) | ((bytes[offset_byte + 1] & 0x03) << 8);
            data[offset_data + 1] =
                ((bytes[offset_byte + 1] >> 2) & (0x3f)) | ((bytes[offset_byte + 2] & 0x0f) << 6);
            data[offset_data + 2] =
                ((bytes[offset_byte + 2] >> 4) & (0x0f)) | ((bytes[offset_byte + 3] & 0x3f) << 4);
            data[offset_data + 3] =
                ((bytes[offset_byte + 3] >> 6) & (0x03)) | ((bytes[offset_byte + 4] & 0xff) << 2);
        }

        poly
    }

    /// A nearly verbatim copy of the C reference impl of POL2BS_N where N = 2^13
    /// https://github.com/KULeuven-COSIC/SABER/blob/f7f39e4db2f3e22a21e1dd635e0601caae2b4510/Reference_Implementation_KEM/pack_unpack.c#L78
    fn reference_impl_to_bytes_mod8192(polyn: &RingElem, bytes: &mut [u8]) {
        let mut offset_byte: usize;
        let mut offset_data: usize;
        let data = polyn.0;

        for j in 0..RING_DEG / 8 {
            offset_byte = 13 * j;
            offset_data = 8 * j;
            bytes[offset_byte] = (data[offset_data] & (0xff)) as u8;
            bytes[offset_byte + 1] = ((data[offset_data] >> 8) & 0x1f) as u8
                | ((data[offset_data + 1] & 0x07) << 5) as u8;
            bytes[offset_byte + 2] = ((data[offset_data + 1] >> 3) & 0xff) as u8;
            bytes[offset_byte + 3] = ((data[offset_data + 1] >> 11) & 0x03) as u8
                | ((data[offset_data + 2] & 0x3f) << 2) as u8;
            bytes[offset_byte + 4] = ((data[offset_data + 2] >> 6) & 0x7f) as u8
                | ((data[offset_data + 3] & 0x01) << 7) as u8;
            bytes[offset_byte + 5] = ((data[offset_data + 3] >> 1) & 0xff) as u8;
            bytes[offset_byte + 6] = ((data[offset_data + 3] >> 9) & 0x0f) as u8
                | ((data[offset_data + 4] & 0x0f) << 4) as u8;
            bytes[offset_byte + 7] = ((data[offset_data + 4] >> 4) & 0xff) as u8;
            bytes[offset_byte + 8] = ((data[offset_data + 4] >> 12) & 0x01) as u8
                | ((data[offset_data + 5] & 0x7f) << 1) as u8;
            bytes[offset_byte + 9] = ((data[offset_data + 5] >> 7) & 0x3f) as u8
                | ((data[offset_data + 6] & 0x03) << 6) as u8;
            bytes[offset_byte + 10] = ((data[offset_data + 6] >> 2) & 0xff) as u8;
            bytes[offset_byte + 11] = ((data[offset_data + 6] >> 10) & 0x07) as u8
                | ((data[offset_data + 7] & 0x1f) << 3) as u8;
            bytes[offset_byte + 12] = ((data[offset_data + 7] >> 5) & 0xff) as u8;
        }
    }

    /// A nearly verbatim copy of the C reference impl of BS2POL_N where N = 2
    /// https://github.com/KULeuven-COSIC/SABER/blob/f7f39e4db2f3e22a21e1dd635e0601caae2b4510/Reference_Implementation_KEM/pack_unpack.c#L184
    fn saber_ref_from_bytes_mod2(b: &[u8]) -> RingElem {
        let mut poly = RingElem::default();
        let data = &mut poly.0;

        let b_arr: [u8; 1 * RING_DEG / 8] = b.try_into().unwrap();
        let bytes = b_arr.map(|x| x as u16);

        for j in 0..32 {
            {
                for i in 0..8 {
                    data[j * 8 + i] = (bytes[j] >> i) & 0x01;
                }
            }
        }

        poly
    }

    /// A nearly verbatim copy of the C reference impl of POL2BS_N where N = 2
    /// https://github.com/KULeuven-COSIC/SABER/blob/f7f39e4db2f3e22a21e1dd635e0601caae2b4510/Reference_Implementation_KEM/pack_unpack.c#L196
    fn saber_ref_to_bytes_mod2(polyn: &RingElem, bytes: &mut [u8]) {
        let data = polyn.0;

        for j in 0..32 {
            for i in 0..8 {
                bytes[j] |= ((data[j * 8 + i] & 0x01) << i) as u8;
            }
        }
    }
}
