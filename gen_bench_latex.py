#!/usr/bin/env python3
"""Turn a `target/criterion-<backend>` tree into a LaTeX table body.

Each row is

    <library> & <lvl I> & <lvl III> & <lvl V> \\

where each level group is `<keygen> & <encap> & <decap>`, in microseconds to
three significant digits. Timings are criterion's median point estimate; the
largest standard error of any median that went into the table is reported on
stderr.
"""

import argparse
import json
import math
import sys
from pathlib import Path

TARGET_DIR = Path(__file__).resolve().parent / "target"

# Criterion group directories are named `<library><sep><level>`, e.g. `kopis512`,
# `libcrux_mlkem768`, `graviolamlkem768`.
LEVELS = ("512", "768", "1024")

# Bench (function) directory names, in column order. The keygen bench is not
# named consistently across the harnesses, so accept either spelling.
OPS = (
    ("gen-keypair-derand", "keygen-derand"),
    ("encap-derand",),
    ("decap",),
)

# Prettified row labels; anything unlisted falls back to the raw directory stem.
DISPLAY_NAMES = {
    "kopis": r"\textsf{kopis}",
    "libcrux_serial": r"\textsf{libcrux}",
    "libcrux_avx2": r"\textsf{libcrux}",
    "awslc": r"\textsf{aws-lc-rs}",
    "graviola": r"\textsf{graviola}",
}

# Rows are emitted in this order; libraries not listed here follow, sorted.
ROW_ORDER = ("kopis", "libcrux", "awslc", "graviola")

# Cell contents for a benchmark that was not run.
MISSING = "---"


def split_group(name):
    """Split a criterion group directory name into (library, level).

    Returns None for directories that do not look like a benchmark group.
    """
    for level in LEVELS:
        if name.endswith(level):
            lib = name[: -len(level)]
            # Strip the `mlkem` / `_mlkem` infix that some harnesses carry.
            for suffix in ("_mlkem", "-mlkem", "mlkem"):
                if lib.endswith(suffix):
                    lib = lib[: -len(suffix)]
                    break
            return lib.strip("_-"), level
    return None


def read_median(bench_dir):
    """Read (point estimate, standard error) of the median, in nanoseconds."""
    path = bench_dir / "new" / "estimates.json"
    if not path.is_file():
        return None
    with path.open() as f:
        median = json.load(f)["median"]
    return median["point_estimate"], median["standard_error"]


def find_op(group_dir, aliases):
    for alias in aliases:
        estimate = read_median(group_dir / alias)
        if estimate is not None:
            return estimate
    return None


def sig3(nanos):
    """Format nanoseconds as microseconds with three significant digits.

    Always plain decimal notation: `%g` would flip to exponential past 1000 us,
    which reads badly in a table.
    """
    micros = nanos / 1000.0
    if micros == 0:
        return "0.00"
    magnitude = math.floor(math.log10(abs(micros)))
    decimals = max(0, 2 - magnitude)
    formatted = f"{micros:.{decimals}f}"
    # Rounding can bump the magnitude (9.999 -> 10.00), leaving four digits.
    if decimals and abs(float(formatted)) >= 10 ** (magnitude + 1):
        formatted = f"{micros:.{max(0, decimals - 1)}f}"
    return formatted


def collect(root):
    """Return {library: {level: [(median, stderr) | None, ...]}}, in nanoseconds."""
    table = {}
    for group_dir in sorted(root.iterdir()):
        if not group_dir.is_dir() or group_dir.name == "report":
            continue
        split = split_group(group_dir.name)
        if split is None:
            print(f"warning: skipping unrecognized group {group_dir.name}", file=sys.stderr)
            continue
        lib, level = split
        estimates = [find_op(group_dir, aliases) for aliases in OPS]
        if all(e is None for e in estimates):
            print(f"warning: no timings under {group_dir.name}", file=sys.stderr)
            continue
        table.setdefault(lib, {})[level] = estimates
    return table


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("backend", choices=("serial", "avx2", "neon"))
    args = parser.parse_args()

    root = TARGET_DIR / f"criterion-{args.backend}"
    if not root.is_dir():
        parser.error(f"no such directory: {root}")

    table = collect(root)
    if not table:
        parser.error(f"no benchmark groups found under {root}")

    def row_key(lib):
        rank = ROW_ORDER.index(lib) if lib in ROW_ORDER else len(ROW_ORDER)
        return (rank, lib)

    libs = sorted(table, key=row_key)

    worst = None  # (relative stderr, absolute stderr in ns, label)
    rows = []  # one list of cell strings (MISSING for a bench that was not run) per library
    for lib in libs:
        cells = []
        for level in LEVELS:
            estimates = table[lib].get(level)
            for i, aliases in enumerate(OPS):
                estimate = None if estimates is None else estimates[i]
                if estimate is None:
                    cells.append(MISSING)
                    continue
                median, stderr = estimate
                cells.append(sig3(median))
                candidate = (stderr / median, stderr, f"{lib}{level}/{aliases[0]}")
                if worst is None or candidate > worst:
                    worst = candidate
        rows.append(cells)

    # Bold the fastest entry in each column. The comparison is on the printed value rather than
    # the raw median, so a column whose winners tie at three significant digits bolds all of them
    # instead of arbitrarily picking the one that happened to round down.
    for column in range(len(LEVELS) * len(OPS)):
        printed = [row[column] for row in rows if row[column] != MISSING]
        if not printed:
            continue
        best = min(printed, key=float)
        for row in rows:
            if row[column] == best:
                row[column] = rf"\textbf{{{best}}}"

    for lib, cells in zip(libs, rows):
        label = DISPLAY_NAMES.get(lib)
        print(" & ".join([label] + cells) + r" \\")

    if worst is not None:
        relative, stderr, label = worst
        print(
            "\n"
            f"max standard error of the median: {stderr / 1000.0:.3g} us "
            f"({relative * 100:.2f}% of the median, at {label})",
            file=sys.stderr,
        )


if __name__ == "__main__":
    main()
