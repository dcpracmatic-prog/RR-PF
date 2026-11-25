/-
  Literals: the closed forms behind `MNE.parse` and `MNE.from_float`.

  parse (src/rr_pf/core.py), for text  [-] I . F [R]  with |F| = f digits and
  |R| = p digits, and P = int(I ++ F), full = int(I ++ F ++ R):
      value = sign * (full - P) / (10^f * (10^p - 1))
  Here `periodicValue P f R p` is the unsigned part.

  Proven here (no `sorry`):
    * periodic_closed     : for p ≥ 1, the value is P/10^f + R/(10^f (10^p - 1))
    * periodic_series     : the repeating tail is the geometric series
                            Σ_k (R/10^(f+p)) (10^-p)^k, so the closed form is its sum
    * den_dyadic_dvd      : (n / 2^k).den divides 2^k
    * den_dyadic_pow_two  : (n / 2^k).den is a power of two

  from_float: `MNE.from_float(x)` is `Fraction(x)`, the exact binary value of x,
  with a zero-width interval. Every float is n / 2^k, so its denominator is a
  power of two (den_dyadic_pow_two). The Python side is tested against
  `float.as_integer_ratio`, which is the same value.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace RRPF.Literals

/-- Unsigned value of a periodic literal `I.F[R]` (prefix P = int(I ++ F),
    f = |F|, R = int of the repeat block, p = |R|). -/
def periodicValue (P f R p : ℕ) : ℚ :=
  ((P : ℚ) * 10 ^ p + R - P) / (10 ^ f * (10 ^ p - 1))

lemma ten_pow_ge_ten {p : ℕ} (hp : 1 ≤ p) : (10 : ℚ) ≤ 10 ^ p := by
  calc (10 : ℚ) = 10 ^ 1 := by norm_num
    _ ≤ 10 ^ p := pow_le_pow_right₀ (by norm_num) hp

lemma ten_pow_pred_pos {p : ℕ} (hp : 1 ≤ p) : (0 : ℚ) < 10 ^ p - 1 := by
  have := ten_pow_ge_ten hp
  linarith

/-- Closed form split into the finite part and the repeating part. -/
theorem periodic_closed (P f R p : ℕ) (hp : 1 ≤ p) :
    periodicValue P f R p = (P : ℚ) / 10 ^ f + (R : ℚ) / (10 ^ f * (10 ^ p - 1)) := by
  have h1 : (10 : ℚ) ^ p - 1 ≠ 0 := (ten_pow_pred_pos hp).ne'
  have h2 : (10 : ℚ) ^ f ≠ 0 := by positivity
  unfold periodicValue
  field_simp
  ring

/-- The repeating tail `Σ_k (R/10^(f+p)) (10^-p)^k` sums (in ℝ) to the closed
    form minus P/10^f. Stated over ℝ because the geometric-series lemma is. -/
theorem periodic_series (P f R p : ℕ) (hp : 1 ≤ p) :
    HasSum (fun k : ℕ => (R : ℝ) / 10 ^ (f + p) * (1 / 10 ^ p) ^ k)
      ((periodicValue P f R p : ℝ) - (P : ℝ) / 10 ^ f) := by
  have hge : (10 : ℝ) ≤ 10 ^ p := by
    calc (10 : ℝ) = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ p := pow_le_pow_right₀ (by norm_num) hp
  have hr0 : (0 : ℝ) ≤ 1 / 10 ^ p := by positivity
  have hr1 : (1 : ℝ) / 10 ^ p < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hs := (hasSum_geometric_of_lt_one hr0 hr1).mul_left ((R : ℝ) / 10 ^ (f + p))
  convert hs using 1
  have h1 : (10 : ℝ) ^ p - 1 ≠ 0 := by
    have : (0 : ℝ) < 10 ^ p - 1 := by linarith
    exact this.ne'
  have h3 : (10 : ℝ) ^ p ≠ 0 := by positivity
  have h2 : (10 : ℝ) ^ f ≠ 0 := by positivity
  have h4 : (1 : ℝ) - 1 / 10 ^ p = (10 ^ p - 1) / 10 ^ p := by
    field_simp
  unfold periodicValue
  rw [h4, pow_add]
  push_cast
  field_simp
  ring

/-- Every denominator of n / 2^k divides 2^k. -/
theorem den_dyadic_dvd (n : ℤ) (k : ℕ) : ((n : ℚ) / 2 ^ k).den ∣ 2 ^ k := by
  have h : (n : ℚ) / 2 ^ k = Rat.divInt n ((2 : ℤ) ^ k) := by
    rw [Rat.divInt_eq_div]
    push_cast
    rfl
  rw [h]
  have := Rat.den_dvd n ((2 : ℤ) ^ k)
  exact_mod_cast this

/-- The denominator of a dyadic rational n / 2^k is a power of two. -/
theorem den_dyadic_pow_two (n : ℤ) (k : ℕ) :
    ∃ j, j ≤ k ∧ ((n : ℚ) / 2 ^ k).den = 2 ^ j := by
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (den_dyadic_dvd n k)
  exact ⟨j, hj, hjeq⟩

/-- Model of `MNE.from_float(q)`: the exact value, with zero radius. -/
def fromFloatBounds (q : ℚ) : ℚ × ℚ := (q, q)

/-- `from_float` introduces no radius: the interval it returns is a point. -/
theorem fromFloat_point (q : ℚ) : fromFloatBounds q = (q, q) := rfl

end RRPF.Literals
