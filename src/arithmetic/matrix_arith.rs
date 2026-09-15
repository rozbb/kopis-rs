//! This file defines and implements matrices over our ring

use crate::{arithmetic::RingElem, consts::RING_DEG};

use zeroize::Zeroize;

/// An element of R^{x×y} where R is a [`RingElem`], stored in row-major order
// We store the matrix in row-major order, so the outer array is the number of rows, i.e., the
// height, i.e., X
#[derive(Eq, PartialEq, Debug, Clone, Zeroize)]
pub(crate) struct Matrix<const X: usize, const Y: usize>(pub(crate) [[RingElem; Y]; X]);

impl<const X: usize, const Y: usize> Default for Matrix<X, Y> {
    fn default() -> Self {
        Matrix([[RingElem::default(); Y]; X])
    }
}

impl<const X: usize, const Y: usize> Matrix<X, Y> {
    /// Applies [`RingElem::shift_right`] to each element in the matrix
    pub(crate) fn shift_right(&mut self, shift: usize) {
        for row in self.0.iter_mut() {
            for elem in row.iter_mut() {
                elem.shift_right(shift)
            }
        }
    }

    /// Adds a given value to all coefficients of all elements of the matrix
    pub(crate) fn wrapping_add_to_all(&mut self, val: u16) {
        for row in self.0.iter_mut() {
            for elem in row.iter_mut() {
                elem.wrapping_add_to_all(val);
            }
        }
    }

    /// Serializes this matrix, ring element by ring element, treating each ring element
    /// coefficient as having only `BITS_PER_ELEM` bits.
    pub(crate) fn serialize<const BITS_PER_ELEM: usize>(&self, out_buf: &mut [u8]) {
        assert_eq!(out_buf.len(), X * Y * BITS_PER_ELEM * RING_DEG / 8);

        /* More idiomatic version here. We have to use explicit indices because aeneas (the Lean
         * extractor) has a problem with some iterator patterns
        let mut chunk_iter = out_buf.chunks_mut(BITS_PER_ELEM * RING_DEG / 8);
        for row in self.0.iter() {
            for entry in row.iter() {
                let out_chunk = chunk_iter
                    .next()
                    .expect("length check at beginning ensures X*Y many chunks");
                entry.serialize::<BITS_PER_ELEM>(out_chunk);
        */
        let chunk_len = BITS_PER_ELEM * RING_DEG / 8;
        for i in 0..X {
            for j in 0..Y {
                let idx = i * Y + j;
                let out_chunk = &mut out_buf[idx * chunk_len..(idx + 1) * chunk_len];
                self.0[i][j].serialize::<BITS_PER_ELEM>(out_chunk);
            }
        }
    }

    /// Deserializes a matrix of R10 values, element by element
    pub(crate) fn deserialize_10(bytes: &[u8]) -> Self {
        assert_eq!(bytes.len(), X * Y * 10 * RING_DEG / 8);
        let mut result = Matrix::default();

        /* More idiomatic version here. We have to use explicit indices because aeneas (the Lean
         * extractor) has a problem with some iterator patterns
        let mut chunk_iter = bytes.chunks(bits_per_elem * RING_DEG / 8);
        for row in result.0.iter_mut() {
            for entry in row.iter_mut() {
                let chunk = chunk_iter
                    .next()
                    .expect("length check at beginning ensures X*Y many chunks");
                *entry = RingElem::deserialize(chunk, bits_per_elem);
             }
        }
        */
        let chunk_len = 10 * RING_DEG / 8;
        for i in 0..X {
            for j in 0..Y {
                let idx = i * Y + j;
                let chunk = &bytes[idx * chunk_len..(idx + 1) * chunk_len];
                result.0[i][j] = RingElem::deserialize::<10>(chunk);
            }
        }

        result
    }
}
