#!/usr/bin/env python3
"""Regenerate Kopis/Avx2/Keccak/RoundSpec.lean from the extracted `keccak::round`.

`round` is 208 intrinsic operations written out at literal indices (aeneas cannot execute an
array access at a computed index, so the Rust is unrolled).  Its proof is 60 `have`s that fold
each register into the spec's vocabulary, and hand-writing those is neither pleasant nor safe:
a transposed register name would still typecheck against the wrong lemma instance in some cases.

So the proof body is derived from the extracted body instead.  The generator re-derives every
fact rather than transcribing it, and asserts as it goes:

  * the five column folds read src[x], src[x+5], src[x+10], src[x+15], src[x+20];
  * each theta mixing term is xor(c[x-1], rotl 1 c[x+1]);
  * each `chi_row!` temporary's (source index, rotation) pair picks out **exactly one** (y, x) in
    `rustTable` — so a transcription slip in either the Rust or the table fails here, loudly;
  * each output is xor(t_x, andnot(t_{x+1}, t_{x+2})) with the t's from the right row.

Run from the `lean/` directory:  python3 scripts/gen_round_spec.py > Kopis/Avx2/Keccak/RoundSpec.lean
"""
import re, sys

EXTRACT = "ExtractedRustAvx2.lean"

def parse_round():
    src = open(EXTRACT).read().split("\n")
    start = next(i for i, l in enumerate(src) if l.startswith("def backend.avx2.keccak.round\n") or
                 l.strip() == "def backend.avx2.keccak.round")
    end = next(i for i in range(start + 1, len(src)) if src[i].startswith("/--"))
    body = src[start:end]
    read, xor, andn, rotl, mod, dread, upd = {}, {}, {}, {}, {}, {}, []
    pending = None
    for ln in body:
        s = ln.strip()
        m = re.match(r"let (\w+) ← Array\.index_usize src (\d+)#usize", s)
        if m: read[m.group(1)] = int(m.group(2)); continue
        m = re.match(r"let (\w+) ← backend\.avx2\.intrinsics\.xor_si256 (\w+) (\w+)", s)
        if m: xor[m.group(1)] = (m.group(2), m.group(3)); continue
        m = re.match(r"let (\w+) ← backend\.avx2\.intrinsics\.andnot_si256 (\w+) (\w+)", s)
        if m: andn[m.group(1)] = (m.group(2), m.group(3)); continue
        m = re.match(r"let (\w+) ← backend\.avx2\.keccak\.rotl (\d+)#i32 (\d+)#i32 (\w+)", s)
        if m: rotl[m.group(1)] = (int(m.group(2)), m.group(4)); continue
        m = re.match(r"let (\w+) ← (\d+)#usize % 5#usize", s)
        if m: mod[m.group(1)] = int(m.group(2)); continue
        m = re.match(r"let (\w+) ←$", s)
        if m: pending = m.group(1); continue
        m = re.match(r"Array\.index_usize \(Array\.make 5#usize \[ ([^\]]+) \]\) (\w+)", s)
        if m: dread[pending] = (m.group(2), [t.strip() for t in m.group(1).split(",")]); continue
        m = re.match(r"let (\w+) ← Array\.update (\w+) (\w+) (\w+)", s)
        if m: upd.append((m.group(1), m.group(2), m.group(3), m.group(4))); continue
    assert (len(read), len(andn), len(upd)) == (25, 25, 25), (len(read), len(andn), len(upd))
    return read, xor, andn, rotl, mod, dread, upd

read, xor, andn, rotl, mod, dread, upd = parse_round()

out = []
A = out.append

# ---- 1. column parities -------------------------------------------------
# c{x} = xor(P, a4);  P = xor(Q,R);  Q = xor(a0,a1);  R = xor(a2,a3)
for x in range(5):
    c = f"c{x}"
    P, a4 = xor[c]
    Q, R = xor[P]
    a0, a1 = xor[Q]
    a2, a3 = xor[R]
    srcs = [a0, a1, a2, a3, a4]
    assert [read[s] for s in srcs] == [x, x+5, x+10, x+15, x+20], (x, [read[s] for s in srcs])
    reads = " ".join(f"(lane_read src {x} {j} {s} {s}_post)" for j, s in enumerate(srcs))
    A(f"  have hc{x} : ∀ i, lane64 {c} i = parity (stateWords src i) {x} :=")
    A(f"    parity_of src {x} {c} {' '.join(srcs)}")
    A(f"      {reads}")
    A(f"      (by rw [{c}_post, {P}_post, {Q}_post, {R}_post])")

# ---- 2. theta mixing terms ---------------------------------------------
dreg = {}
for n, (a, b) in xor.items():
    if re.fullmatch(r"c\d", a) and b in rotl:
        amt, cr = rotl[b]
        assert amt == 1
        x = (int(a[1]) + 1) % 5
        assert cr == f"c{(x+1)%5}", (n, a, cr, x)
        dreg[x] = n
        A(f"  have hd{x} : ∀ i < 4, lane64 {n} i = dTerm (stateWords src i) {x} :=")
        A(f"    dTerm_of src {x} {a} {cr} {b} {n} hc{a[1]} hc{(x+1)%5} {b}_post {n}_post")

# ---- 3. the chi_row temporaries ----------------------------------------
# t = rotl amt w ; w = xor(a, m) ; m = dread(i) ; a = read
RUST = [[(0,0),(6,44),(12,43),(18,21),(24,14)],
        [(3,28),(9,20),(10,3),(16,45),(22,61)],
        [(1,1),(7,6),(13,25),(19,8),(20,18)],
        [(4,27),(5,36),(11,10),(17,15),(23,56)],
        [(2,62),(8,55),(14,39),(15,41),(21,2)]]
treg = {}
seen = set()
for t, (amt, w) in rotl.items():
    if w not in xor: continue
    a, m = xor[w]
    if m not in dread or a not in read: continue
    iname, _ = dread[m]
    k = read[a]
    # locate (y,x) from the rust table
    yx = [(y, x) for y in range(5) for x in range(5) if RUST[y][x] == (k, amt)]
    assert len(yx) == 1, (t, k, amt, yx)
    y, x = yx[0]
    assert (y, x) not in seen; seen.add((y, x))
    treg[(y, x)] = t
    xs, ys = x, y
    src_x = (x + 3*y) % 5          # the column whose d-term is used
    assert k % 5 == src_x
    A(f"  have hm{t} : {m} = {dreg[src_x]} := by simp only [{m}_post, {iname}_post]; rfl")
    A(f"  have ht{t} : ∀ i < 4, lane64 {t} i = tVal (stateWords src i) {ys} {xs} :=")
    A(f"    tVal_of src {ys} {xs} {a} {dreg[src_x]} {w} {t}")
    A(f"      (lane_read src {(x+3*y)%5} {(k//5)} {a} {a}_post)")
    A(f"      hd{src_x} (by rw [{w}_post, hm{t}])")
    A(f"      (by exact {t}_post)   -- rustTable[{ys}][{xs}].2 reduces to {amt}")
assert len(seen) == 25, len(seen)

# ---- 4. the chi_row outputs --------------------------------------------
vreg = {}
for j, (dstN, prev, iname, val) in enumerate(upd):
    y, x = j // 5, j % 5
    t0 = treg[(y, x)]
    a, w = xor[val]
    assert a == t0, (val, a, t0)
    t1, t2 = andn[w]
    assert t1 == treg[(y, (x+1) % 5)] and t2 == treg[(y, (x+2) % 5)]
    vreg[(y, x)] = val
    A(f"  have hv{val} : ∀ i < 4, lane64 {val} i = chiRow (stateWords src i) {y} {x} :=")
    A(f"    chiRow_of src {y} {x} {t0} {t1} {t2} {w} {val}")
    A(f"      ht{t0} ht{t1} ht{t2} {w}_post {val}_post")

FOLDS = "\n".join(out) + "\n"

# ---- 5. emit the file ---------------------------------------------------
dsts = ", ".join(f"{d}_post" for d, _, _, _ in reversed(upd))
idxs = ", ".join(f"{i}_post" for _, _, i, _ in upd)
CHAIN = f"""simp +decide only [{dsts},
        Std.Array.set_val_eq, {idxs},
        getElem!_list_set, List.length_set, hdlen,
        Nat.reduceMul, Nat.reduceAdd, if_true, if_false]"""

HEADER = open("scripts/round_spec_header.txt").read().rstrip("\n")

parts = [HEADER, """theorem round_spec (src dst : Std.Array Vec256 25#usize) (rc : Vec256) (iᵣ l : ℕ)
    (hl : l < 4) (hrc : ∀ i < 4, lane64 rc i = rcWord iᵣ) :
    backend.avx2.keccak.round src dst rc
      ⦃ (r : Std.Array Vec256 25#usize) => ∀ x y : Fin 5,
          stateWords r l x y = RndW (stateWords src l) iᵣ x y ⦄ := by
  unfold backend.avx2.keccak.round
  step*
  rename_i x y""", FOLDS, f"""  have hd25len : (dst25.val : List Vec256).length = 25 := dst25.property
  have hdlen : (dst.val : List Vec256).length = 25 := dst.property
  have hz : ((0#usize : Std.Usize) : \u2115) = 0 := rfl
  have h150 : v150 = (dst25.val)[0]! :=
    v150_post.trans (getElem!_pos _ 0 (by rw [hd25len]; decide)).symm
  have h00 : lane64 v151 l = chiRow (stateWords src l) 0 0 ^^^ rcWord i\u1d63 := by
    have hv150 : lane64 v150 l = lane64 v61 l := by
      rw [h150]
      {CHAIN}
    have hx : lane64 v151 l = lane64 v150 l ^^^ lane64 rc l := by
      simp only [lane64, v151_post, lane64_xor_bits]
    rw [hx, hv150, hvv61 l hl, hrc l hl]
  fin_cases x <;> fin_cases y <;>
    simp +decide only [stateWords_apply, idx, r_post, {dsts},
      Std.Array.set_val_eq, {idxs}, getElem!_list_set, List.length_set, hdlen, hz,
      Nat.reduceMul, Nat.reduceAdd, if_true, if_false]"""]
for n in range(25):
    x, y = n // 5, n % 5
    parts.append("  \u00b7 rw [h00, RndW_fused]; simp +decide" if (x, y) == (0, 0)
                 else f"  \u00b7 simp +decide [RndW_fused, hv{vreg[(y, x)]} l hl]")
parts.append("\nend\n\nend Kopis.Avx2.Keccak")
sys.stdout.write("\n".join(parts) + "\n")
