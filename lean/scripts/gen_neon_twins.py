#!/usr/bin/env python3
"""Generate Kopis/Neon/Properties/*.lean from Kopis/Properties/*.lean.

The NEON twin of `scripts/gen_avx2_twins.py`, and deliberately derived from it: the two backends
have the *same* six runtime-dispatch points, so the AVX2 patch list is reused with the backend
name swapped rather than transcribed.  Only where the two genuinely differ does this file say
anything of its own, and those places are collected in `OVERRIDES` below.

**What is renamed and what is not.**  A patch is a pair (serial anchor, backend replacement).
The anchor is serial text and must stay untouched — renaming it would stop it matching.  Only
the replacement is renamed, and the same goes for the file body: the four substitutions the AVX2
generator makes are the only ones that are safe.  In particular the serial sources themselves
mention `Kopis.Avx2.NttAlg`, `Kopis.Avx2.q1`, `Kopis/Avx2/Crt.lean` and friends — the two-prime
algebra lives on the AVX2 side and is shared, not duplicated — so a blanket `Avx2 -> Neon` over
the body would point them at modules that do not exist.

**Where the backends differ.**  `backend::avx2::cpu::available` is a real CPUID probe, so the
AVX2 patches case-split on it and prove the same postcondition on both branches.
`backend::neon::cpu::available` is `cfg!(target_arch = "aarch64")`, which extracts to a literal
`ok true`: every dispatch resolves at elaboration time, the portable branch is unreachable, and
the patch is a `rw` rather than a `cases`.  That also means NEON has no `available_ok`
assumption to carry in its trust base.
"""
import importlib.util, pathlib, re, sys

def _load(name):
    spec = importlib.util.spec_from_file_location(
        name, pathlib.Path(__file__).with_name(name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

avx2 = _load("gen_avx2_twins")
bridge = _load("gen_avx2_bridge")

SRC = pathlib.Path("Kopis/Properties")
DST = pathlib.Path("Kopis/Neon/Properties")

# Applied to *replacement* text only — never to a serial anchor, and never to a file body.
RENAMES = [("Kopis.Avx2", "Kopis.Neon"), ("Kopis/Avx2", "Kopis/Neon"),
           ("backend.avx2", "backend.neon"), ("backend::avx2", "backend::neon"),
           ("RustKopisAvx2", "RustKopisNeon"), ("ExtractedRustAvx2", "ExtractedRustNeon"),
           ("AVX2", "NEON"), ("avx2", "neon"), ("Avx2", "Neon")]


def rename(t: str) -> str:
    for old, new in RENAMES:
        t = t.replace(old, new)
    return t


# The anchors are serial text *after* the AVX2 converter's own four substitutions, so the three
# that name a module have to be swapped in the anchor as well; nothing else in an anchor may be.
ANCHOR_RENAMES = [("Kopis.Avx2.Properties", "Kopis.Neon.Properties"),
                  ("RustKopisAvx2", "RustKopisNeon"),
                  ("ExtractedRustAvx2", "ExtractedRustNeon")]


def anchor(t: str) -> str:
    for old, new in ANCHOR_RENAMES:
        t = t.replace(old, new)
    return t


PATCHES = [(mod, anchor(old), rename(new)) for mod, old, new in avx2.PATCHES]
EXTRA_IMPORTS = {k: [rename(v) for v in vs] for k, vs in avx2.EXTRA_IMPORTS.items()}
# `pointwise_mul_acc_neon` lives in `Kopis/Neon/MulT.lean`, not in `Reduce.lean` where the AVX2
# twin finds its counterpart.
EXTRA_IMPORTS["NttBridge.lean"] = EXTRA_IMPORTS["NttBridge.lean"] + ["Kopis.Neon.MulT"]
_ELEM = [(anchor(old), rename(new), cnt) for old, new, cnt in bridge._ELEM]
_MUL = [(anchor(old), rename(new), cnt) for old, new, cnt in bridge._MUL]
_BRIDGE = [(anchor(old), rename(new), cnt) for old, new, cnt in bridge._BRIDGE]

def _indent(t: str, n: int) -> str:
    return "".join((" " * n + l if l.strip() else l) for l in t.splitlines(keepends=True))


def patch_secret_loop(t: str) -> str:
    """`sample::gen_secret_from_seed_loop`'s arity and its three-way guard.

    aeneas hoisted the compile-time-`true` `cpu::available` out of the loop, so the NEON loop
    takes an extra leading `Bool`; and its body chooses between the portable `cbd` and
    `cbd_lanes`.  `step*` walks into that guard and leaves three goals — byte-aligned `MU`, and
    flag-clear, are the serial proof verbatim; the third is `cbd_lanes` with an `Array.update`
    write-back, which `neon_cbd_eq` turns into the first.  So the serial script is reused three
    times over, with one rewrite in front of the odd one.
    """
    for name in ("gen_secret_from_seed_loop_spec", "gen_secret_from_seed_loop_bd"):
        old = f"theorem {name} {{L : Usize}} (MU : Usize)\n    (iter :"
        new = f"theorem {name} {{L : Usize}} (MU : Usize) (b : Bool)\n    (iter :"
        assert t.count(old) == 1, name
        t = t.replace(old, new)
        assert t.count(f"{name} MU iter1") == 1, name
        t = t.replace(f"{name} MU iter1", f"{name} MU _ iter1")
        assert t.count(f"{name} MU {{ start :=") == 1, name
        t = t.replace(f"{name} MU {{ start :=", f"{name} MU _ {{ start :=")
    assert t.count("    sample.gen_secret_from_seed_loop MU iter seed secret buf") == 2
    t = t.replace("    sample.gen_secret_from_seed_loop MU iter seed secret buf",
                  "    sample.gen_secret_from_seed_loop MU b iter seed secret buf")
    # the three arms
    out = []
    rest = t
    while True:
        k = rest.find("    step*\n")
        if k < 0:
            out.append(rest)
            break
        stop = rest.index("  · let* ⟨ o, iter1, hnone, _ ⟩", k)
        script = rest[k + len("    step*\n"):stop]
        # The script runs three times over, so a *named* synthetic hole would be created more
        # than once under the same `all_goals`.  Anonymous holes are positional, and the scripts
        # already dispatch on them with bullets.
        script = re.sub(r"\?[A-Za-z_][A-Za-z0-9_']*", "?_", script)
        # The odd arm samples *before* it stores, and stores with `Array.update` rather than the
        # `index_mut` closure, so its copy of the script needs the `cbd` call moved in front of
        # the `step*` that walks the store, and the store's name swapped.
        armed = _indent(script, 2)
        j = armed.index("      let* ⟨ re1, hre1 ⟩ ← cbd_")
        eol = armed.index("\n", j) + 1
        cbd_line = armed[j:eol].replace(" buf1 re hMU", " buf1 (Std.Array.repeat 256#usize 0#u16) hMU")
        armed = (armed[:j]
                 + "      rw [Kopis.Neon.neon_cbd_eq buf1 MU (Std.Array.repeat 256#usize 0#u16)\n"
                   "        hMU hbuf1_len]\n"
                 + cbd_line
                 + "      let* ⟨ a, index_mut_back, a_post1, a_post2 ⟩ ←\n"
                   "        Array.index_mut_usize_spec secret iter.start\n"
                   "          (by have := secret.property; scalar_tac)\n"
                   "      let* ⟨ a1, a1_post ⟩ ← Array.update_spec\n"
                 + armed[eol:]
                   .replace("(index_mut_back (index_mut_back1 re1))", "(index_mut_back a1)")
                   .replace("(index_mut_back1 re1)", "a1")
                   .replace("re_post2, harr0", "a1_post, harr0"))
        arm = ("    step*\n"
               "    case h1 =>\n" + armed
               + "    all_goals\n" + _indent(script, 2))
        out.append(rest[:k] + arm)
        rest = rest[stop:]
    return "".join(out)


POST_TRANSFORMS = {
    "GenSecretTop.lean": patch_secret_loop,
    "NttCrtElem.lean": lambda t: bridge._apply(_ELEM, t, "NttCrtElem"),
    "NttCrtMul.lean": lambda t: bridge._apply(_MUL, t, "NttCrtMul"),
    "NttBridge.lean": lambda t: bridge._apply(_BRIDGE, t, "NttBridge"),
}

HEADER = ("-- AUTOGENERATED from Kopis/Properties/%s by `make generated`.  Do not edit.\n"
          "-- See NEON_VERIFICATION_PLAN.md phase E: the serial proof, with the extracted\n"
          "-- constants and this stack's namespace renamed, and nothing else changed.\n")

# ---------------------------------------------------------------------------------------
# NEON-only replacements, applied *after* the renamed AVX2 patches.
#
# Each is (module, old, new, count).  `old` is matched against the already-patched text, so it is
# written in NEON spelling.  A count that does not match fails the generator loudly.
# ---------------------------------------------------------------------------------------

OVERRIDES = [
    # Every dispatch patch opens with `obtain ⟨b, hb⟩ := available_ok`, the AVX2 assumption that
    # the CPUID probe returns.  NEON's probe is `cfg!(target_arch = "aarch64")`, which extracts to
    # a literal `ok true`, so the same existential is a `rfl` — and NEON carries no `available_ok`
    # in its trust base.  The case split is left in place: both branches are genuinely provable
    # (the `false` one is the serial proof), and collapsing it would mean deleting the rest of the
    # theorem rather than changing one line.
    (mod, f"obtain ⟨{b}, {hb}⟩ := Kopis.Neon.available_ok",
     f"obtain ⟨{b}, {hb}⟩ : ∃ b, backend.neon.cpu.available = ok b := ⟨true, rfl⟩", cnt)
    for mod, b, hb, cnt in [("GenMatrix.lean", "b1", "hb1", 1),
                            ("GenSecretTop.lean", "bAvx", "hbAvx", 1),
                            ("GenSecretTop.lean", "bNeon", "hbNeon", 1),
                            ("NttCrtElem.lean", "b", "hb", 2),
                            ("Ntt.lean", "bU", "hbU", 1),
                            ("NttBridge.lean", "bb", "hbb", 3)]
] + [
    # The NEON matrix sampler batches two entries per `xof2` call, not four, so its `Usize`
    # headroom hypothesis is `+ 2` where the AVX2 one is `+ 4`.  The callers' `+ 4` is stronger.
    ("GenMatrix.lean",
     "neon_gen_matrix_from_seed_spec L seed hLmax",
     "neon_gen_matrix_from_seed_spec L seed (by omega)", 1),
    # The NEON secret sampler batches too, so it needs `Usize` headroom rather than AVX2's
    # `L ≤ 4` (which came from AVX2 covering every row in a single four-way `xof4` call).
    # `L < 256` — already a hypothesis of every caller — gives it.
    ("GenSecretTop.lean",
     "neon_gen_secret_from_seed_spec L MU seed hMU hL hL4",
     "neon_gen_secret_from_seed_spec L MU seed hMU (by scalar_tac)", 1),
    ("GenSecretTop.lean",
     "neon_gen_secret_from_seed_bd L MU seed hMU hL hL4",
     "neon_gen_secret_from_seed_bd L MU seed hMU (by scalar_tac)", 1),
    ("Ntt.lean",
     "neon_gen_matrix_from_seed_bd L seed hLmax",
     "neon_gen_matrix_from_seed_bd L seed (by omega)", 1),
    # The four NTT dispatch targets take no `available = ok true` hypothesis on NEON — the probe
    # *is* `ok true` — and two of them are spelled without the backend suffix the AVX2 names
    # carry.  Everything else about the calls is unchanged: `IScalar.val` is `bv.toInt` by
    # definition, so the `.val` statements and AVX2's `i16View`/`i32View` ones are defeq.
    ("NttCrtElem.lean",
     "Kopis.Neon.from_uniform_NttOK hb elem", "Kopis.Neon.elem_from_uniform_NttOK elem", 1),
    ("NttCrtElem.lean",
     "Kopis.Neon.from_secret_NttOK hb elem", "Kopis.Neon.elem_from_secret_NttOK elem", 1),
    ("NttBridge.lean",
     "Kopis.Neon.reduce_invntt_to_ring_elem_avx hbb N hN",
     "Kopis.Neon.reduce_invntt_to_ring_elem_neon N hN", 1),
    ("NttBridge.lean",
     "Kopis.Neon.pointwise_mul_acc_avx hbb acc", "Kopis.Neon.pointwise_mul_acc_neon acc", 2),
]


def convert(text: str, name: str) -> str:
    out = text.replace("RustKopisSerial", "RustKopisNeon")
    out = out.replace("ExtractedRustSerial", "ExtractedRustNeon")
    # `import Kopis.Bits.Stream` must NOT be renamed: it is shared.
    out = out.replace("import Kopis.Bits.Stream", "import Kopis.Bits.Stream@KEEP@")
    out = out.replace("Kopis.Properties", "Kopis.Neon.Properties")
    out = out.replace("import Kopis.Bits.Stream@KEEP@", "import Kopis.Bits.Stream")
    if "import Kopis.Bits.Stream" not in out:
        first_import = re.search(r"(?m)^import [^\n]*$", out)
        if first_import:
            out = (out[:first_import.start()] + "import Kopis.Bits.Stream\n"
                   + out[first_import.start():])
    out = re.sub(r"(?m)^namespace Kopis\.Neon\.Properties$",
                 "namespace Kopis.Neon.Properties\n\nopen Kopis.Properties ("
                 + avx2.SHARED + ")", out, count=1)
    for mod, old, new in PATCHES:
        if mod != name:
            continue
        if out.count(old) != 1:
            raise SystemExit(
                f"gen_neon_twins: patch for {mod} does not apply "
                f"({out.count(old)} matches). The serial proof changed; update PATCHES.")
        out = out.replace(old, new, 1)
    if name in POST_TRANSFORMS:
        out = POST_TRANSFORMS[name](out)
    for mod, old, new, cnt in OVERRIDES:
        if mod != name:
            continue
        got = out.count(old)
        if got != cnt:
            raise SystemExit(
                f"gen_neon_twins: override for {mod} matched {got} times (want {cnt}). "
                f"Anchor starts: {old[:90]!r}")
        out = out.replace(old, new)
    for extra in EXTRA_IMPORTS.get(name, []):
        first_import = re.search(r"(?m)^import [^\n]*$", out)
        out = out[:first_import.start()] + f"import {extra}\n" + out[first_import.start():]
    return HEADER % name + out


def main() -> int:
    DST.mkdir(parents=True, exist_ok=True)
    names = sorted(p.name for p in SRC.glob("*.lean"))
    written = 0
    for name in names:
        if avx2.write_if_changed(DST / name, convert((SRC / name).read_text(), name)):
            written += 1
    if avx2.write_if_changed(pathlib.Path("Kopis/Neon/Properties.lean"),
                             "-- AUTOGENERATED by `make twins`.  Do not edit.\n"
                             + "".join(f"import Kopis.Neon.Properties.{n[:-5]}\n"
                                       for n in names)):
        written += 1
    stale = [q for q in sorted(DST.glob("*.lean")) if q.name not in names]
    for q in stale:
        q.unlink()
    if written or stale:
        print(f"neon twins: {written} written, {len(names) + 1 - written} unchanged, "
              f"{len(stale)} removed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
