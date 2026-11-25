#!/usr/bin/env python3
"""Export Python results as Lean cases: lean/RRPF/Cases.lean.

Python computes the outputs of ``MNE.sqrt``, ``MNE.parse`` and
``MNE.from_float`` on a fixed, seeded set of inputs. This script writes each
(input, output) pair as a Lean theorem. ``lake build`` then checks every case
against the Lean model, so a disagreement between the two sides fails the build.

Usage:
    python tools/export_cases.py            # rewrite lean/RRPF/Cases.lean
    python tools/export_cases.py --check    # exit 1 if the committed file is stale

Determinism: a fixed seed, ``random.Random.getrandbits`` only (its stream is
stable across Python versions), no timestamps, no dict/set ordering. CI runs
``--check`` and fails on any diff.

What each case certifies:
  sqrt exact    lo <= sqrt(v) <= hi and hi - lo <= 10^-d   (sqrt_cert)
  sqrt interval L <= sqrt(x) <= U for all x in [a, b]      (sqrt_interval_cert)
  parse         sign * periodicValue(P, f, R, p) = MNE.parse(text).exact
  from_float    (n / 2^k).den = 2^k, with (n, 2^k) = float.as_integer_ratio()
"""
from __future__ import annotations

import argparse
import math
import random
import struct
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "lean" / "RRPF" / "Cases.lean"
SEED = 20260701

# Make `rr_pf` importable from a source checkout as well as an installed package.
sys.path.insert(0, str(ROOT / "src"))
from rr_pf import MNE  # noqa: E402


class Rng:
    """Seeded generator using only getrandbits, whose stream is version-stable."""

    def __init__(self, seed: int):
        self._r = random.Random(seed)

    def int_in(self, lo: int, hi: int) -> int:
        return lo + self._r.getrandbits(48) % (hi - lo + 1)

    def bits(self, n: int) -> int:
        return self._r.getrandbits(n)


def qlit(q: Fraction) -> str:
    """Lean literal for a rational, e.g. ((-3 : ℚ) / 7)."""
    if q.denominator == 1:
        return f"({q.numerator} : ℚ)"
    return f"(({q.numerator} : ℚ) / {q.denominator})"


def _sqrt_inputs(rng: Rng):
    fixed = [Fraction(0), Fraction(1), Fraction(2), Fraction(4, 9),
             Fraction(49, 100), Fraction(1, 3), Fraction(10**6 + 7, 97),
             Fraction(1, 10**12)]
    random_vals = []
    for _ in range(14):
        num = rng.int_in(0, 10**6)
        den = rng.int_in(1, 10**4)
        random_vals.append(Fraction(num, den))
    squares = []
    for _ in range(4):
        a = rng.int_in(1, 500)
        b = rng.int_in(1, 500)
        squares.append(Fraction(a * a, b * b))
    return fixed + random_vals + squares


DIGITS = [0, 1, 2, 3, 5, 8]


def sqrt_cases(rng: Rng):
    exact_lines, interval_lines = [], []
    for i, v in enumerate(_sqrt_inputs(rng)):
        d = DIGITS[i % len(DIGITS)]
        res = MNE(v).sqrt(d)
        lo, hi = res.bounds()
        assert lo >= 0 and hi >= 0
        w = Fraction(1, 10**d)
        assert hi - lo <= w, (v, d, lo, hi)
        exact_lines.append(
            f"theorem sqrtExact_{i} :\n"
            f"  SqrtCert {qlit(lo)} {qlit(hi)} {qlit(v)} {qlit(w)} :=\n"
            f"  sqrt_cert (by norm_num) (by norm_num) (by norm_num) (by norm_num)"
            f" (by norm_num)"
        )
    intervals = []
    for _ in range(8):
        a = Fraction(rng.int_in(0, 10**5), rng.int_in(1, 999))
        b = a + Fraction(rng.int_in(0, 10**4), rng.int_in(1, 999))
        intervals.append((a, b))
    intervals.append((Fraction(2), Fraction(2)))
    intervals.append((Fraction(0), Fraction(1, 2)))
    for i, (a, b) in enumerate(intervals):
        c = (a + b) / 2
        r = (b - a) / 2
        res = MNE(c, r).sqrt(20)
        L, U = res.bounds()
        interval_lines.append(
            f"theorem sqrtInterval_{i} :\n"
            f"  SqrtInterval {qlit(a)} {qlit(b)} {qlit(L)} {qlit(U)} :=\n"
            f"  fun x h1 h2 => sqrt_interval_cert (by norm_num) (by norm_num)"
            f" (by norm_num) (by norm_num) h1 h2"
        )
    return exact_lines, interval_lines


PARSE_FIXED = ["0.[3]", "1.[0]", "-0.[9]", "2.5[0]", "12.[34]", ".[6]",
               "0.1[6]", "3.14(15)", "-7.(81)"]


def _digits(rng: Rng, n: int) -> str:
    return "".join(str(rng.int_in(0, 9)) for _ in range(n))


def parse_cases(rng: Rng):
    texts = list(PARSE_FIXED)
    for _ in range(18):
        sign = "-" if rng.int_in(0, 1) else ""
        whole = _digits(rng, rng.int_in(0, 3))
        finite = _digits(rng, rng.int_in(0, 3))
        rep = _digits(rng, rng.int_in(1, 4))
        open_, close = ("[", "]") if rng.int_in(0, 1) else ("(", ")")
        texts.append(f"{sign}{whole}.{finite}{open_}{rep}{close}")
    lines = []
    for i, text in enumerate(texts):
        value = MNE.parse(text).exact
        assert value is not None, text
        sign_text = text.strip()
        neg = sign_text.startswith("-")
        body = sign_text.lstrip("+-")
        whole, rest = body.split(".", 1)
        finite, rep_block = rest.split(("[" if "[" in rest else "("), 1)
        rep = rep_block.rstrip("])")
        P = int(((whole or "0") + finite) or "0")
        f = len(finite)
        R = int(rep)
        p = len(rep)
        sgn = -1 if neg else 1
        assert value == sgn * Fraction(P * 10**p + R - P, 10**f * (10**p - 1)), text
        lines.append(
            f"-- parse {text!r}\n"
            f"theorem parse_{i} :\n"
            f"  ({sgn} : ℚ) * periodicValue {P} {f} {R} {p} = {qlit(value)} := by\n"
            f"  unfold periodicValue; norm_num"
        )
    return lines


def _float_inputs(rng: Rng):
    fixed = [0.0, 0.1, 0.5, -3.75, 1e-300, 5e-324, 1.7976931348623157e308,
             -0.0, 2.0**-1074 * 3, 1.0 / 3.0]
    out = list(fixed)
    while len(out) < len(fixed) + 16:
        x = struct.unpack("<d", rng.bits(64).to_bytes(8, "little"))[0]
        if math.isfinite(x):
            out.append(x)
    return out


def float_cases(rng: Rng):
    lines = []
    for i, x in enumerate(_float_inputs(rng)):
        n, d = x.as_integer_ratio()
        assert d & (d - 1) == 0, (x, d)  # a power of two
        k = d.bit_length() - 1
        # from_float(x) is Fraction(x): the same value as n / 2^k
        assert Fraction(x) == Fraction(n, 1 << k)
        lines.append(
            f"-- from_float {x!r}\n"
            f"theorem fromFloat_{i} :\n"
            f"  (((({n} : ℤ) : ℚ)) / 2 ^ {k}).den = 2 ^ {k} := by norm_num"
        )
    return lines


HEADER = """\
/-
  GENERATED by tools/export_cases.py (seed {seed}). Do not edit by hand.
  CI regenerates this file and fails on any diff.

  Each theorem is one exported Python result, checked here against the Lean
  model. A disagreement between Python and Lean fails `lake build`.
-/
import RRPF.Sqrt
import RRPF.Literals

namespace RRPF.Cases
open RRPF.Sqrt RRPF.Literals
"""


def render() -> str:
    rng = Rng(SEED)
    exact_lines, interval_lines = sqrt_cases(rng)
    parse = parse_cases(rng)
    floats = float_cases(rng)
    parts = [HEADER.format(seed=SEED)]
    parts.append("\n/-! ### sqrt: exact inputs (Python `MNE(v).sqrt(d)`) -/\n")
    parts.append("\n\n".join(exact_lines) + "\n")
    parts.append("\n/-! ### sqrt: interval inputs (Python `MNE(c, r).sqrt(20)`) -/\n")
    parts.append("\n\n".join(interval_lines) + "\n")
    parts.append("\n/-! ### parse: periodic literals (Python `MNE.parse`) -/\n")
    parts.append("\n\n".join(parse) + "\n")
    parts.append("\n/-! ### from_float: dyadic denominators (Python `as_integer_ratio`) -/\n")
    parts.append("\n\n".join(floats) + "\n")
    parts.append("\nend RRPF.Cases\n")
    return "".join(parts)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true",
                    help="do not write; exit 1 if the committed file differs")
    args = ap.parse_args(argv)
    text = render()
    if args.check:
        current = OUT.read_text(encoding="utf-8") if OUT.exists() else ""
        if current != text:
            print(f"{OUT} is stale: run python tools/export_cases.py", file=sys.stderr)
            return 1
        print(f"{OUT} is up to date")
        return 0
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(text, encoding="utf-8")
    print(f"wrote {OUT} ({text.count('theorem ')} theorems)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
