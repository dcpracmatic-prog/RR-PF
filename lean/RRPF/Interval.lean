/-
  RInterval: the Lean counterpart of the Python class `MNE` (src/rr_pf/core.py).

  Python stores two endpoints `_lo`, `_hi` (over ℚ). Here they are reals; the
  rational case is an instance, so every statement below covers the Python
  computations on rational inputs.

  The map to the model is `toBN : RInterval → BoundedNum`:
    val   := (lo + hi) / 2     -- Python `center`
    bound := (hi - lo) / 2     -- Python `radius`

  Proven here (no `sorry`):
    * mem_iff      : t ∈ [lo, hi]  ↔  isValid (toBN I) t
    * toBN_gap     : 0 ∉ [lo, hi]  →  bound < |val|   (the hypothesis of BoundedNum.div)
    * toBN_add     : add/sub commute with the map, exactly (val and bound)
    * mul_hull_sound : the Python product interval lies inside the
                       BoundedNum.mul enclosure
    * div_hull_sound : the Python quotient interval lies inside the
                       BoundedNum.div enclosure

  "Inside" is containment of the Python endpoints in the Lean enclosure,
  i.e. Python ⊆ Lean. The Lean enclosure is coarser than the exact hull.
-/

import Mathlib.Tactic
import RRPF.BoundedNum

noncomputable section

namespace RRPF

/-- Closed real interval `[lo, hi]`. Mirrors the Python `MNE` endpoints. -/
structure RInterval where
  lo : ℝ
  hi : ℝ
  le : lo ≤ hi

namespace RInterval

/-- Python `MNE.center` and `MNE.radius` as the Lean model `(val, bound)`. -/
def toBN (I : RInterval) : BoundedNum :=
  { val := (I.lo + I.hi) / 2
    bound := (I.hi - I.lo) / 2
    nonneg_bound := div_nonneg (sub_nonneg.mpr I.le) (by norm_num) }

theorem toBN_val (I : RInterval) : I.toBN.val = (I.lo + I.hi) / 2 := rfl
theorem toBN_bound (I : RInterval) : I.toBN.bound = (I.hi - I.lo) / 2 := rfl

/-! ### Operations, transcribed from core.py -/

/-- Python `__neg__`: `_from_bounds(-hi, -lo)`. -/
def neg (I : RInterval) : RInterval :=
  ⟨-I.hi, -I.lo, by linarith [I.le]⟩

/-- Python `__add__`: endpoints add. -/
def add (I J : RInterval) : RInterval :=
  ⟨I.lo + J.lo, I.hi + J.hi, add_le_add I.le J.le⟩

/-- Python `__sub__`: `self + (-other)`. -/
def sub (I J : RInterval) : RInterval :=
  add I (neg J)

def min4 (a b c d : ℝ) : ℝ := min (min (min a b) c) d
def max4 (a b c d : ℝ) : ℝ := max (max (max a b) c) d

theorem le_min4 {x a b c d : ℝ} (ha : x ≤ a) (hb : x ≤ b) (hc : x ≤ c) (hd : x ≤ d) :
    x ≤ min4 a b c d :=
  le_min (le_min (le_min ha hb) hc) hd

theorem max4_le {x a b c d : ℝ} (ha : a ≤ x) (hb : b ≤ x) (hc : c ≤ x) (hd : d ≤ x) :
    max4 a b c d ≤ x :=
  max_le (max_le (max_le ha hb) hc) hd

theorem min4_le_max4 (a b c d : ℝ) : min4 a b c d ≤ max4 a b c d :=
  le_trans (show min4 a b c d ≤ a by simp [min4, min_le_iff])
    (show a ≤ max4 a b c d by simp [max4, le_max_iff])

/-- Python `__mul__`: min and max over the four corner products. -/
def mul (I J : RInterval) : RInterval :=
  ⟨min4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi),
   max4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi),
   min4_le_max4 _ _ _ _⟩

/-- Python `__truediv__` step 1: `_from_bounds(min(1/lo, 1/hi), max(1/lo, 1/hi))`. -/
def recip (J : RInterval) : RInterval :=
  ⟨min (1 / J.lo) (1 / J.hi), max (1 / J.lo) (1 / J.hi),
   (min_le_left _ _).trans (le_max_left _ _)⟩

/-- Python `__truediv__`: `self * reciprocal`. Python raises ZeroDivisionError when
    `other._lo <= 0 <= other._hi`; that is the hypothesis `h`. -/
def div (I J : RInterval) (_h : ¬ (J.lo ≤ 0 ∧ 0 ≤ J.hi)) : RInterval :=
  mul I (recip J)

/-! ### Membership and the division hypothesis -/

/-- Membership in `[lo, hi]` is exactly validity of the model pair. -/
theorem mem_iff (I : RInterval) (t : ℝ) :
    (I.lo ≤ t ∧ t ≤ I.hi) ↔ BoundedNum.isValid I.toBN t := by
  unfold BoundedNum.isValid
  rw [toBN_val, toBN_bound, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- If 0 is not in `[lo, hi]` then the radius is strictly below |center|.
    This is the hypothesis `y.bound < |y.val|` of `BoundedNum.div`. -/
theorem toBN_gap (I : RInterval) (h : ¬ (I.lo ≤ 0 ∧ 0 ≤ I.hi)) :
    I.toBN.bound < |I.toBN.val| := by
  rw [toBN_val, toBN_bound]
  by_cases hp : 0 < I.lo
  · rw [abs_of_pos (show (0 : ℝ) < (I.lo + I.hi) / 2 by linarith [I.le])]
    linarith
  · have hn : I.hi < 0 := by
      by_contra hc
      exact h ⟨not_lt.mp hp, not_lt.mp hc⟩
    rw [abs_of_neg (show (I.lo + I.hi) / 2 < 0 by linarith)]
    linarith

/-! ### Exact correspondence for add and sub -/

/-- add commutes with the map: the model val and bound are the sums. -/
theorem toBN_add (I J : RInterval) :
    (add I J).toBN.val = (BoundedNum.add I.toBN J.toBN).val ∧
    (add I J).toBN.bound = (BoundedNum.add I.toBN J.toBN).bound := by
  constructor
  · show ((I.lo + J.lo) + (I.hi + J.hi)) / 2 = (I.lo + I.hi) / 2 + (J.lo + J.hi) / 2
    ring
  · show ((I.hi + J.hi) - (I.lo + J.lo)) / 2 = (I.hi - I.lo) / 2 + (J.hi - J.lo) / 2 + 0
    ring

/-- sub commutes with the map: val is the difference, bound is the sum of bounds
    (as in BoundedNum.sub, whose bound is x.bound + y.bound). -/
theorem toBN_sub (I J : RInterval) :
    (sub I J).toBN.val = (BoundedNum.sub I.toBN J.toBN).val ∧
    (sub I J).toBN.bound = (BoundedNum.sub I.toBN J.toBN).bound := by
  constructor
  · show ((I.lo + -J.hi) + (I.hi + -J.lo)) / 2 =
      (BoundedNum.add I.toBN (BoundedNum.approx (-J.toBN.val) J.toBN.bound J.toBN.nonneg_bound)).val
    show ((I.lo + -J.hi) + (I.hi + -J.lo)) / 2 =
      (I.lo + I.hi) / 2 + -((J.lo + J.hi) / 2)
    ring
  · show ((I.hi + -J.lo) - (I.lo + -J.hi)) / 2 =
      (I.hi - I.lo) / 2 + (J.hi - J.lo) / 2 + 0
    ring

/-! ### Hull containment: Python result ⊆ Lean enclosure -/

/-- Every Python product endpoint lies in the BoundedNum.mul enclosure. -/
theorem mul_hull_sound (I J : RInterval) :
    (BoundedNum.mul I.toBN J.toBN).val - (BoundedNum.mul I.toBN J.toBN).bound
        ≤ (mul I J).lo ∧
    (mul I J).hi ≤
        (BoundedNum.mul I.toBN J.toBN).val + (BoundedNum.mul I.toBN J.toBN).bound := by
  have key : ∀ x y : ℝ, I.lo ≤ x → x ≤ I.hi → J.lo ≤ y → y ≤ J.hi →
      (BoundedNum.mul I.toBN J.toBN).val - (BoundedNum.mul I.toBN J.toBN).bound ≤ x * y ∧
      x * y ≤ (BoundedNum.mul I.toBN J.toBN).val + (BoundedNum.mul I.toBN J.toBN).bound := by
    intro x y hx1 hx2 hy1 hy2
    have hv : BoundedNum.isValid (BoundedNum.mul I.toBN J.toBN) (x * y) :=
      BoundedNum.mul_valid I.toBN J.toBN x y ((mem_iff I x).mp ⟨hx1, hx2⟩)
        ((mem_iff J y).mp ⟨hy1, hy2⟩)
    unfold BoundedNum.isValid at hv
    rw [abs_le] at hv
    constructor <;> linarith [hv.1, hv.2]
  constructor
  · show _ ≤ min4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi)
    exact le_min4 (key I.lo J.lo le_rfl I.le le_rfl J.le).1
      (key I.lo J.hi le_rfl I.le J.le le_rfl).1
      (key I.hi J.lo I.le le_rfl le_rfl J.le).1
      (key I.hi J.hi I.le le_rfl J.le le_rfl).1
  · show max4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi) ≤ _
    exact max4_le (key I.lo J.lo le_rfl I.le le_rfl J.le).2
      (key I.lo J.hi le_rfl I.le J.le le_rfl).2
      (key I.hi J.lo I.le le_rfl le_rfl J.le).2
      (key I.hi J.hi I.le le_rfl J.le le_rfl).2

/-- Every Python quotient endpoint lies in the BoundedNum.div enclosure.
    The hypothesis `h` is the Python ZeroDivisionError guard. -/
theorem div_hull_sound (I J : RInterval) (h : ¬ (J.lo ≤ 0 ∧ 0 ≤ J.hi)) :
    (BoundedNum.div I.toBN J.toBN (toBN_gap J h)).val
        - (BoundedNum.div I.toBN J.toBN (toBN_gap J h)).bound ≤ (div I J h).lo ∧
    (div I J h).hi ≤
        (BoundedNum.div I.toBN J.toBN (toBN_gap J h)).val
          + (BoundedNum.div I.toBN J.toBN (toBN_gap J h)).bound := by
  have key : ∀ x y : ℝ, I.lo ≤ x → x ≤ I.hi → J.lo ≤ y → y ≤ J.hi →
      (BoundedNum.div I.toBN J.toBN (toBN_gap J h)).val
        - (BoundedNum.div I.toBN J.toBN (toBN_gap J h)).bound ≤ x / y ∧
      x / y ≤ (BoundedNum.div I.toBN J.toBN (toBN_gap J h)).val
        + (BoundedNum.div I.toBN J.toBN (toBN_gap J h)).bound := by
    intro x y hx1 hx2 hy1 hy2
    have hv : BoundedNum.isValid (BoundedNum.div I.toBN J.toBN (toBN_gap J h)) (x / y) :=
      BoundedNum.div_valid I.toBN J.toBN x y ((mem_iff I x).mp ⟨hx1, hx2⟩)
        ((mem_iff J y).mp ⟨hy1, hy2⟩) (toBN_gap J h)
    unfold BoundedNum.isValid at hv
    rw [abs_le] at hv
    constructor <;> linarith [hv.1, hv.2]
  -- A corner of I × recip(J) is x * r with r = 1/y for an endpoint y of J.
  have bc : ∀ (x r : ℝ), (I.lo ≤ x ∧ x ≤ I.hi) → (r = 1 / J.lo ∨ r = 1 / J.hi) →
      (BoundedNum.div I.toBN J.toBN (toBN_gap J h)).val
          - (BoundedNum.div I.toBN J.toBN (toBN_gap J h)).bound ≤ x * r ∧
      x * r ≤ (BoundedNum.div I.toBN J.toBN (toBN_gap J h)).val
          + (BoundedNum.div I.toBN J.toBN (toBN_gap J h)).bound := by
    intro x r hx hr
    rcases hr with rfl | rfl
    · rw [mul_one_div]; exact key x J.lo hx.1 hx.2 le_rfl J.le
    · rw [mul_one_div]; exact key x J.hi hx.1 hx.2 J.le le_rfl
  have rlo : (recip J).lo = 1 / J.lo ∨ (recip J).lo = 1 / J.hi := min_choice _ _
  have rhi : (recip J).hi = 1 / J.lo ∨ (recip J).hi = 1 / J.hi := max_choice _ _
  have hI1 : I.lo ≤ I.lo ∧ I.lo ≤ I.hi := ⟨le_rfl, I.le⟩
  have hI2 : I.lo ≤ I.hi ∧ I.hi ≤ I.hi := ⟨I.le, le_rfl⟩
  constructor
  · show _ ≤ min4 (I.lo * (recip J).lo) (I.lo * (recip J).hi)
        (I.hi * (recip J).lo) (I.hi * (recip J).hi)
    exact le_min4 (bc I.lo _ hI1 rlo).1 (bc I.lo _ hI1 rhi).1
      (bc I.hi _ hI2 rlo).1 (bc I.hi _ hI2 rhi).1
  · show max4 (I.lo * (recip J).lo) (I.lo * (recip J).hi)
        (I.hi * (recip J).lo) (I.hi * (recip J).hi) ≤ _
    exact max4_le (bc I.lo _ hI1 rlo).2 (bc I.lo _ hI1 rhi).2
      (bc I.hi _ hI2 rlo).2 (bc I.hi _ hI2 rhi).2

end RInterval
end RRPF
end
