# Lean 4 – RRPF

Model of bounded numbers and rational/real interval arithmetic, with proofs of
soundness and of the correspondence used by the Python package.

```bash
cd lean
lake exe cache get   # fetch the Mathlib cache (optional, speeds up the first build)
lake build           # must end with "Build completed successfully"
```

Toolchain (`lean-toolchain`): Lean `v4.14.0`. Mathlib pinned to `v4.14.0`
in `lakefile.toml`.

## Layout

- `RRPF/BoundedNum.lean`: `BoundedNum` as a pair `(val, bound)`, read as the
  set of `t` with `|t - val| ≤ bound`. Operations `add`, `sub`, `mul`, `div`,
  and the theorems `add_valid`, `sub_valid`, `mul_valid`, `div_valid`,
  `add_exact`, `mul_exact`, `div_exact`, `add_mono_bound`.
- `RRPF/Interval.lean`: `RInterval` (closed real interval `[lo, hi]`), the map
  `toBN` to `(val, bound)`, interval `add`, `sub`, `mul`, `div`, and the
  theorems `mem_iff`, `toBN_gap`, `toBN_add`, `toBN_sub`, `mul_hull_sound`,
  `div_hull_sound`.
- `RRPF.lean`: root module; imports both files above.

The library is named `RRPF` because Lake needs a Lean identifier for the
library name, and the package name `rr-pf` contains a hyphen.

## Axioms

Run `#print axioms <name>` on any theorem above. The output lists only
`propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry`.

## Sandboxes where `tar` cannot change ownership

If `lake exe cache get` fails with `Cannot change ownership to uid ...`, put a
`tar` wrapper that adds `--no-same-owner` first on the `PATH`:

```bash
mkdir -p /tmp/tarshim
printf '#!/bin/sh\nexec /usr/bin/tar --no-same-owner "$@"\n' > /tmp/tarshim/tar
chmod +x /tmp/tarshim/tar
export PATH="/tmp/tarshim:$PATH"
lake exe cache get
```

See [`../docs/CORRESPONDENCE.md`](../docs/CORRESPONDENCE.md) for how these
theorems relate to the Python code.
