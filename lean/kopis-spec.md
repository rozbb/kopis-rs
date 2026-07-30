# Kopis KEM Specification

In this doc we define the Kopis key encapsulation mechanism (KEM). We do this in two parts, first defining an IND-CPA-secure public key encryption (PKE) scheme, then defining the IND-CCA-secure KEM via the Fujisaki-Okamoto transform.

# Preliminaries

We first specify all the algorithms, syntax, and mathematics we will need for the specification.

## Dependencies

We use the TurboSHAKE XOF family defined in [RFC 9861](https://www.rfc-editor.org/rfc/rfc9861.html). We invoke it as `TurboSHAKE128/TurboSHAKE256(M, L, D)`, where `M` is the message to be hashed, `L` is the desired output length, and `D` is the domain separator in the range `[0x01, 0x7f]`.

## Syntax

We use pseudocode resembling a mix of Rust and Python. Function definitions are preceded with `fn`, each function input name is followed by a colon, then the type signature, and each function  is followed by an arrow `->` then the return type. Ranges are denoted `a..b`, and indicate the range `[a, b)` (i.e., including `a`, excluding `b`). When `s` is a sequence type (e.g., a bitstring or bytestring), `s[a..b]` is used to denote the subsequence starting at index `a` (0-indexed), and ending at and excluding index `b`. We use infix `||` to denote concatenation of bytestrings. We use infix `^` to denote integer exponentiation when the inputs are expressions, and to denote vector types when the LHS input is a type (e.g., `ℤ^N` denotes the vector space of dimension `N` over the integers). We write `[uK; N]` to mean an array of `N` many `K`-bit integers. Subtraction over `uK` is always defined as wrapping subtraction, e.g., `0u8 - 1u8 = 255u8`.

## Mathematical Definitions

Let `R` be the negacyclic polynomial ring `ℤ[X]/(X²⁵⁶ + 1)`. We denote by `R13` the polynomial ring modulo `2^13`, i.e., `R/2¹³R` (this is isomorphic to `(ℤ/2¹³ℤ)[X]/(X²⁵⁶ + 1)`). Similarly, `R10` denotes `R/2¹⁰R` and `R1` denotes `R/2R`.

`MatRn` refers to an `ℓ×ℓ` matrix of `Rn` elements. `VecRn` refers to a vector of `ℓ` many `Rn` elements. `make_r13` refers to the natural morphism from the space of coefficients `[u13; 256]` to `R13` (input is interpreted lowest-degree-coefficient-first). `make_r10` is defined similarly for `R10`. `make_mat13` takes a nested array `[[R13; ℓ]; ℓ]` and interprets it as a list of rows in a matrix in `MatR13`. `transpose` transposes the given matrix. `make_vec13` takes an array `[R13; ℓ]` and interprets it as a column vector in `VecR13`, in the same order as `make_mat13`, i.e., such that `make_mat13([eye, zeros, ... zeros]) * make_vec13(eye) = make_vec13(eye)`, where `eye = [1, 0, ..., 0]` , and `zeros = [0, 0, ..., 0]` (interpreting the numbers as ring elements). When indexing into a vector `v: VecRn`, we do so in the same order that was used in its constructor, i.e., `v[i]` equals `a[i]` where `a` is the input to the `make_vecn` that constructed `v`.

When we write `r as U` for some type U, we mean to invoke either the natural injection or projection of `r` into/onto U. For example, if `r` is in `R10^ℓ` and `U` is `R13^ℓ`, then it is the natural injection, and if vice-versa, then it is the natural projection by quotienting by `2¹⁰R13`.

For any modulus `N`, we say the canonical form of an element of `ℤ/Nℤ` is its representative integer in `[0, N)`. For any `n` and a ring element `r` we say its _canonical coefficients_ `canonical_coeffs(r: Rn) -> [un; 256]` are the unique sequence of 256 `un` values `a_0, ..., a_255` such that `r = a_255 X^255 + ... + a_1 X + a_0`.

For an element `r` in `Rn` and integer `N`, we define the right-shift `r >> N` as `make_rn([a_0 >> N, a_1 >> N, ..., a_255 >> N])` where `a_i` are the canonical coefficients of `r`. We define left-shift `r << N` similarly, with coefficients reduced mod `2^n`. We define right and left shift for elements of `VecRn` as operating element-wise.

We define `to_bits_le(n: ℤ, k: un) -> [bool; n]` to be the function that converts an `n`-bit integer to its bit representation, starting with the least significant bit. Similarly, we define 
`from_bits_le(n: ℤ, bits: [bool; n]) -> un` to interpret `n` bits as a `un` value, using `bits[0]` as the least significant bit of the output, and so on.

# Main Algorithms

We now define a **public key encryption (PKE) scheme**. For the purposes of this specification, the secret key space is simply `[u8; 32]`, and generating a fresh secret key amounts to generating a fresh uniform bytestring. We define a public key encryption scheme as the set of the following algorithms:

* `SkToPk(sk) -> pk` — Computes the public key corresponding to the given secret key
* `PkeEncrypt(randomness, pk, msg) -> ct` — Encrypts the given message `msg` to public key `pk`, using encryption randomness `randomness`
* `PkeDecrypt(sk, ct) -> msg` — Decrypts the given ciphertext `ct` using the secret key `sk`, and unconditionally returns a message `msg`

We now define a **key encapsulation mechanism (KEM)**. Similar to the PKE above, secret keys are uniform elements of `[u8; 32]`. A KEM is defined as the set of the following algorithms:

* `SkToPk(sk) -> pk` — Computes the public key corresponding to the given secret key
* `Encap(randomness, pk) -> (k, ct)` — Encapsulates a shared secret `k` to public key `pk`, using randomness `randomness`. Outputs a `k` and a ciphertext `ct`.
* `Decap(sk, ct) -> k` — Decrypts the ciphertext `ct` using the secret key `sk`, and unconditionally returns a shared secret `k`

For real-world usage of these algorithms, the `randomness` parameters above MUST be sampled uniformly.

## Parameters

The following variables represent security parameters, and depend on the security level being instantiated:

* `ℓ` — The public matrix dimension. This impacts the size of public keys and ciphertexts
* `μ` — The binomial parameter used for secret generation
* `t` — The base-2 logarithm of the modulus of the space of compressed ring elements

## Constants

We define the constants used in our implementation. The size in bytes of our secret keys, public keys, and ciphertexts are functions of the parameters above:

* `SK_SIZE = 32`
* `PK_SIZE = 256*ℓ*10/8 + 32`
* `CT_SIZE = 256*t/8 + 256*ℓ*10/8`

We also require domain separators for all our TurboSHAKE invocations:

* `DOMSEP_KGEXPAND = 0x01`
* `DOMSEP_GENMAT = 0x02`
* `DOMSEP_GENSEC = 0x03`
* `DOMSEP_PKHASH = 0x04`
* `DOMSEP_FO = 0x05`
* `DOMSEP_NOREJECT = 0x06`

## PKE

We define key generation, encryption, and decryption for the Kopis IND-CPA-secure PKE scheme. We will define the helper functions later.

```
fn SkToPk(sk: [u8; 32]) -> [u8; PK_SIZE]:
  let (_, _, pk, _) = ExpandDecapKey(sk)
  return pk

fn PkeEncrypt(
  seed: [u8; 32],
  pk: [u8; PK_SIZE],
  msg: [u8; 32]
) -> [u8; CT_SIZE]:
  let vec_b = deserialize_vec(10, pk[..256*ℓ*10/8])
  let mat_seed = pk[256*ℓ*10/8..]
  let m = deserialize_elem(1, msg)

  let mat_A = GenMat(mat_seed)
  let vec_sprime = GenSecret(seed)
  let vec_bprime = RoundToR10(mat_A * vec_sprime)
  let vprime = transpose(vec_b) * (vec_sprime as R10^ℓ)
  let cm = RoundToRt(vprime - ((m as R10) << 9))

  return serialize_vec(10, vec_bprime) || serialize_elem(t, cm)

fn PkeDecrypt(sk: [u8; 32], c: [u8; CT_SIZE]) -> [u8; 32]:
  let (vec_s, ...) = ExpandDecapKey(sk)
  let vec_bprime = deserialize_vec(10, c[..256*ℓ*10/8])
  let cm = deserialize_elem(t, c[256*ℓ*10/8..])
  let v = transpose(vec_bprime) * (vec_s as R10^ℓ)
  let cm10 = (cm as R10) << (10 - t)
  let mprime = RoundToR1(v - cm10)
  return serialize_elem(1, mprime)
```

## KEM

We define the IND-CCA-secure Kopis KEM below. The `SkToPk` function is identical to the one given in the PKE above.

```
fn KemEncap(
  randomness: [u8; 32],
  pk: [u8; PK_SIZE]
) -> ([u8; 32], [u8; CT_SIZE]):
  let pkh = TurboSHAKE256(pk, 32, DOMSEP_PKHASH)
  
  let b = TurboSHAKE256(randomness || pkh, 64, DOMSEP_FO);
  let (k, r) = (b[..32], b[32..])
  let c = PkeEncrypt(r, pk, randomness)
  
  return (k, c)

fn KemDecap(sk: [u8; 32], c: [u8; CT_SIZE]) -> [u8; 32]:
  let (_, z, pk, pkh) = ExpandDecapKey(sk)
  
  let randomness = PkeDecrypt(sk, c)
  let b = TurboSHAKE256(randomness || pkh, 64, DOMSEP_FO);
  let (k, rprime) = (b[..32], b[32..])
  let cprime = PkeEncrypt(rprime, pk, randomness)
  
  if c == cprime:
    return k
  else:
    return TurboSHAKE256(z || c, 32, DOMSEP_NOREJECT)
```

The output of `KemDecap` requires branching based on the equality of two bytestrings. An implementation MUST perform this equality check and return statement in constant time.

For efficiency, implementers MAY internally cache the expanded decapsulation key. But this expanded key SHOULD NOT be saved to disk.

## Auxiliary Functions

We now define the auxiliary functions used in the schemes above:

```
fn ExpandDecapKey(
  sk: [u8; 32]
) -> (VecR13, [u8; 32], [u8; PK_SIZE], [u8; 32]):
  let randomness = TurboSHAKE256(sk || (ℓ as u8), 96, DOMSEP_KGEXPAND)
  let mat_seed = randomness[..32]
  let secret_seed = randomness[32..64]
  let z = randomness[64..]

  let mat_A = GenMat(mat_seed)
  let vec_s = GenSecret(secret_seed)
  let vec_b = RoundToR10(transpose(mat_A) * vec_s)
  let pk = serialize_vec(10, vec_b) || mat_seed
  let pkh = TurboSHAKE256(pk, 32, DOMSEP_PKHASH)

  return (vec_s, z, pk, pkh)

fn RoundToR10(v: R13^ℓ) -> R10^ℓ:
  let h1 = make_r13([4u13; 256])
  let h = make_vec13([h1; ℓ])
  let s = (v + h) >> 3
  return (s as R10^ℓ)

fn RoundToRt(r: R10) -> Rt:
  let h1 = make_r10([4u10; 256])
  let s = (r + h1) >> (10 - t)
  return (s as Rt)

fn RoundToR1(r: R10) -> R1:
  let h2 = make_r10([2^8 - 2^(10-t-1) + 4; 256])
  let s = (r + h2) >> 9
  return (s as R1)

fn GenMat(seed: [u8; 32]) -> MatR13:
  let A: [[R13; ℓ]; ℓ]
  for i in 0u8..ℓ:
    for j in 0u8..ℓ:
      let buf = TurboSHAKE128(seed || i || j, 256*13/8, DOMSEP_GENMAT)
      A[i][j] = deserialize_elem(13, buf)
  return make_mat13(A)

fn GenSecret(seed: [u8; 32]) -> VecR13:
  let s: [R13; ℓ]
  for i in 0u8..ℓ:
    let buf = TurboSHAKE256(seed || i, μ*256/8, DOMSEP_GENSEC)
    let vals = bit_slices(buf)
    let r: [u13; 256]
    for k in 0..256:
      r[k] = hamming(vals[2*k]) - hamming(vals[2*k+1])
    s[i] = make_r13(r)
  return s

# Serializes an element of Rn (for any choice n=13,10,1,t)
fn serialize_elem(n: ℤ, r: Rn) -> [u8; 256*n/8]:
  let a = canonical_coeffs(r)
  let b = to_bits_le(n, a[0]) || ... || to_bits_le(n, a[255])
  let out =
    from_bits_le(8, b[0..8])
    || ... 
    || from_bits_le(8, b[8*(32*n-1)..8*32*n])
  return out

# Serializes an element of VecRn (for any choice n=13,10,1,t)
fn serialize_vec(n: ℤ, v: VecRn) -> [u8; ℓ*256*n/8]:
  let out = serialize_elem(n, v[0]) || ... || serialize_elem(n, v[ℓ-1])
  return out

# Deserializes an element of Rn (for any choice n=13,10,1,t)
fn deserialize_elem(n: ℤ, bytes: [u8; 256*n/8]) -> Rn:
  let b = to_bits_le(8, bytes[0]) || ... || to_bits_le(8, bytes[32*n-1])
  let a: [un; 256]
  for i in 0..256:
    a[i] = from_bits_le(n, b[n*i..n*(i+1)])
  return make_rn(a)

# Deserializes an element of VecRn (for any choice n=13,10,1,t)
fn deserialize_vec(n: ℤ, bytes: [u8; ℓ*256*n/8]) -> VecRn:
  let a: [Rn; ℓ]
  for i in 0..ℓ:
    a[i] = deserialize_elem(n, bytes[i*32*n..(i+1)*32*n])
  return make_vecn(a)

# Reinterprets a bytestring as a sequence of bitstrings of length μ/2
fn bit_slices(bytes: [u8; μ*256/8]) -> [[bool; μ/2]; 512]:
  let b =
    to_bits_le(8, bytes[0])
    || ...
    || to_bits_le(8, bytes[μ*32-1])
  let out: [[bool; μ/2]; 512]
  for i in 0..512:
    out[i] = b[i*μ/2..(i+1)*μ/2]
  return out

# Returns the number of set bits in b
fn hamming(b: [bool; μ/2]) -> u13:
  let out = 0
  for i in 0..μ/2:
    if b[i]:
      out += 1
  return out
```

# Parameter Sets

We define three security levels for Kopis: Kopis-512, Kopis-768, and Kopis-1024, referring to dimension of the public key vector over `ℤ/2¹⁰ℤ`:

|Name       | Parameters     | `PK_SIZE` | `CT_SIZE` |
|---------- |----------------|-----------|-----------|
|Kopis-512  | `ℓ=2 t=3 μ=10` | 672       | 736       |
|Kopis-768  | `ℓ=3 t=4 μ=8 ` | 992       | 1088      |
|Kopis-1024 | `ℓ=4 t=6 μ=6 ` | 1312      | 1472      |
