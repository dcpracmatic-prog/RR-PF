# Correspondence between the Python intervals and the Lean model

This document says exactly what is proven, what is tested, and in which
direction each claim holds. It is meant to be read together with
`lean/RRPF/Interval.lean` and `tests/test_correspondence.py`.

## 1. The two sides

**Python** (`src/rr_pf/core.py`, class `MNE`). A value is a closed rational
interval stored as two `Fraction` endpoints `_lo <= _hi`. A plain rational `x`
is the degenerate interval `[x, x]`.

**Lean** (`lean/RRPF/BoundedNum.lean`). A value is a pair `(val, bound)` with
`bound >= 0`, read as the set of `t` with `|t - val| <= bound`
(`BoundedNum.isValid`). Operations `add`, `sub`, `mul`, `div` propagate bounds.

**Lean bridge** (`lean/RRPF/Interval.lean`). `RInterval` mirrors `MNE` over
`ℝ`. The map to the model is

    toBN [lo, hi] = (val := (lo + hi) / 2, bound := (hi - lo) / 2)

This is `MNE.center` and `MNE.radius` in Python. The inverse is `lo = val - bound`,
`hi = val + bound`, so the map is a bijection between intervals and pairs with
`bound >= 0`.

The Python class is over `ℚ`. The Lean statements are over `ℝ`. Every
rational input is a real input, and every rational operation is a real
operation, so each Lean theorem also covers the Python computation on rationals.

## 2. What is proven in Lean (no `sorry`, axioms only `propext`, `Classical.choice`, `Quot.sound`)

| Lean name | Statement | Python counterpart |
|---|---|---|
| `RInterval.mem_iff` | `lo ≤ t ≤ hi  ↔  isValid (toBN I) t` | `contains`, and `bounds()` |
| `RInterval.toBN_gap` | `¬(lo ≤ 0 ≤ hi)  →  bound < \|val\|` | the guard `other._lo <= 0 <= other._hi` in `__truediv__` |
| `RInterval.toBN_add` | `add` gives `val` sum and `bound` sum, exactly | `__add__` |
| `RInterval.toBN_sub` | `sub` gives `val` difference and `bound` sum, exactly | `__sub__` (as `self + (-other)`) |
| `RInterval.mul_hull_sound` | Python product endpoints lie in `[val - bound, val + bound]` of `BoundedNum.mul` | `__mul__` |
| `RInterval.div_hull_sound` | Python quotient endpoints lie in `[val - bound, val + bound]` of `BoundedNum.div` | `__truediv__` |
| `BoundedNum.add_valid`, `mul_valid`, `sub_valid`, `div_valid` | the `isValid` propagation theorems | used by the two `_sound` theorems |

### Direction of each claim

- **add, sub: equality.** The model pair of the Python result equals the pair
  computed by the Lean operation. No information is lost or gained.
- **mul, div: containment (Python ⊆ Lean).** The Python result interval
  is contained in the Lean enclosure. The Lean enclosure is coarser than the
  exact hull of the Python result, and that is intended: the Lean bound is the
  classical first-order bound, not the tightest one. Python is the tighter
  tool. Do not read the Lean bound as the width of the Python result.

### Why the mul and div proofs do not need convexity

Both `_sound` theorems use only the corners. Python's endpoints are min and max
over corner products (`x*y` for `x` in `{lo, hi}` and `y` in `{lo, hi}`; for
division `x * (1/y)` with `y` in `{lo, hi}`). Each corner is a point of the
form `x*y` or `x/y` with `x` and `y` members of their intervals. Lean's
`mul_valid` / `div_valid` bound every such point. Then `min` is at least the
common lower bound, and `max` is at most the common upper bound, by
`le_min4` and `max4_le`. No claim is made that the Python interval is the
exact hull of the image. Only the inclusion is proven.

## 3. What is only tested (randomized, not proven)

`tests/test_correspondence.py` runs 400 random cases per property (and 100 for
the pointwise samples), with a fixed seed. It checks the **Python code** against
the same statements:

- the map sends add and sub to exact equality;
- membership is preserved by the map;
- the Python product and quotient endpoints lie inside the Lean enclosure;
- the Python zero-division guard fires exactly when `|val| <= bound`;
- sampled points `t*s` and `t/s` lie within the Lean bound.

This is evidence that the *transcription* of the Lean formulas into Python is
right. It is not a proof about the Python source. The Python code is not
extracted from Lean, and nothing forces the two to stay in sync except the
tests. If you change one side, change the other and rerun the tests.

## 4. Out of scope

- `MNE.sqrt`, `MNE.parse`, `MNE.from_float`, and the decimal reading of `MNE(0.1)`.
  None of these are modelled in Lean. `sqrt` has its own rounding logic.
- The Python `__eq__` for a non-degenerate interval, `__str__`, `__repr__`.
- Floating point. `MNE(x)` accepts a float by its decimal representation
  (`MNE(0.1)` is 1/10). `MNE.from_float(x)` uses the exact binary value of `x`.
  The Lean model covers exact rationals only, and `oracle.exact` rejects floats.
- The `ε` rounding term of `BoundedNum.add`/`mul`/`div`. The Python code always
  has `ε = 0`, which is the default in Lean, so the correspondence uses `ε = 0`.

## 5. How to check

```bash
pytest -q                 # Python side, including the correspondence tests
cd lean && lake build     # Lean side, must print "Build completed successfully"
```

To see the axioms of any theorem, add `#print axioms RRPF.RInterval.div_hull_sound`
to a file that imports `RRPF.Interval` and run `lake env lean` on it.
