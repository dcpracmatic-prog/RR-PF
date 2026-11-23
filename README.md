# RR-PF

Exact rational numbers and rational intervals that enclose them, with a
`Fraction`-based test oracle and a Lean 4 model of the interval arithmetic.

Formerly published as `mne`; renamed because that name is taken on PyPI.
The main class is still called `MNE` for API stability.

## Install

```bash
pip install .            # from a clone
pip install ".[test]"    # with pytest
```

## Usage

```python
from fractions import Fraction
from rr_pf import MNE

MNE.parse("0.[3]") * 3          # 1
MNE.parse("0.1[6]")             # 1/6
MNE.parse("0.[142857]")         # 1/7
MNE.parse("-0.25")              # -1/4
MNE(Fraction(4, 9)).sqrt()      # 2/3
MNE.from_float(0.1)             # exact binary value of the float
```

`MNE(0.1)` is the decimal `1/10`, by documented rule.
`MNE.from_float(0.1)` is the binary value `3602879701896397/36028797018963968`.

Division by an interval that contains 0 raises `ZeroDivisionError`.

## Oracle

`rr_pf.oracle` provides an exact sparse matrix-vector product (`ExactCSR`,
`csr_matvec_exact`) for use as a slow reference in other projects' tests.
It rejects `float` entries on purpose, so that a binary/decimal ambiguity
cannot pass silently.

## Lean model

The formal side lives in [`lean/`](lean/). It defines bounded numbers
`(val, bound)` and interval operations over `ℝ`, and proves:

- `add_valid`, `mul_valid`, `sub_valid`, `div_valid`: the bounds are sound;
- `add_exact`, `mul_exact`, `div_exact`, `add_mono_bound`;
- `RInterval.toBN_add`, `toBN_sub`: the Python-style add and sub correspond exactly;
- `RInterval.mul_hull_sound`, `div_hull_sound`: the Python-style mul and div
  results lie inside the Lean enclosure.

No `sorry`. Each theorem depends only on `propext`, `Classical.choice`,
and `Quot.sound`.

[`docs/CORRESPONDENCE.md`](docs/CORRESPONDENCE.md) states, for every claim,
whether it is proven in Lean, only tested in Python, or out of scope, and in
which direction it holds (equality or containment).

## Tests

```bash
pip install ".[test]"
pytest -q
```

The suite has 29 tests. They cover the core arithmetic, the oracle, and a
randomized correspondence check between the Python code and the Lean
formulas (fixed seed).

The oracle test suite includes a mutant that drops small terms. A
float-vs-float comparison misses it for some sizes; the exact oracle catches it.

## Lean build

```bash
cd lean
lake exe cache get   # fetch the Mathlib cache
lake build           # must end with "Build completed successfully"
```

Toolchain: `leanprover/lean4:v4.14.0`, Mathlib `v4.14.0`.

## Continuous integration

`.github/workflows/ci.yml` runs `pytest` on Python and `lake build` on Lean.

## Languages

- English: this file.
- Español: [README.es.md](README.es.md).

## License

See [LICENSE](LICENSE).
