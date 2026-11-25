/-
  Sqrt: the Python `MNE.sqrt` algorithm (src/rr_pf/core.py), modelled over ℚ.

  Python, for a value v ≥ 0 and scale s = 10^digits:
    k     = isqrt((v.numerator * s * s) // v.denominator)
    lower = k / s
    upper = lower            if lower * lower == v
          = (k + 1) / s      otherwise
  and, for an exact input whose numerator and denominator are both perfect
  squares, the exact root sqrt(num)/sqrt(den) (the early branch).

  Proven here (no `sorry`):
    * lower_le_sqrt / sqrt_le_upper : lower ≤ √v ≤ upper            (enclosure)
    * upper_sub_lower_le             : upper - lower ≤ 1/s           (width)
    * upper_eq_lower_of_sq           : exact square → upper = lower
    * exactRoot_sound                : the exact branch returns √v
    * pySqrt_enclosure               : Python `sqrt` on [lo, hi] encloses √x
                                       for every x in [lo, hi]
    * enclosure_of_sq                : certificate form lo² ≤ v ≤ hi² → lo ≤ √v ≤ hi
                                       (used by lean/RRPF/Cases.lean)

  Scope: Python's `isqrt` is modelled by `Nat.sqrt`, which is the same function
  (floor of the square root). That identity is tested, not proven, in Python.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

namespace RRPF.Sqrt

/-- Python: `k = isqrt((numerator * scale * scale) // denominator)`. -/
def kOf (v : ℚ) (s : ℕ) : ℕ :=
  Nat.sqrt ((v.num.toNat * s * s) / v.den)

/-- Python `_sqrt_bounds(value, digits)[0]`. -/
def lower (v : ℚ) (s : ℕ) : ℚ := (kOf v s : ℚ) / s

/-- Python `_sqrt_bounds(value, digits)[1]`: exact when lower² = v. -/
def upper (v : ℚ) (s : ℕ) : ℚ :=
  if lower v s * lower v s = v then lower v s else ((kOf v s : ℚ) + 1) / s

/-- Python exact branch: if numerator and denominator are both perfect squares,
    the root is the exact rational sqrt(num)/sqrt(den). -/
def exactRoot (v : ℚ) : Option ℚ :=
  if Nat.sqrt v.num.toNat * Nat.sqrt v.num.toNat = v.num.toNat ∧
     Nat.sqrt v.den * Nat.sqrt v.den = v.den then
    some ((Nat.sqrt v.num.toNat : ℚ) / (Nat.sqrt v.den : ℚ))
  else none

/-- Python `MNE.sqrt` on the interval [lo, hi] with scale `s`.
    The exact branch runs only when lo = hi, as in `if self.exact is not None`. -/
def pySqrt (lo hi : ℚ) (s : ℕ) : ℚ × ℚ :=
  if lo = hi then
    match exactRoot lo with
    | some r => (r, r)
    | none => (lower lo s, upper lo s)
  else (lower lo s, upper hi s)

/-! ### Integer core -/

lemma num_toNat_cast {v : ℚ} (hv : 0 ≤ v) : (v.num.toNat : ℚ) = v.num := by
  have h : (0:ℤ) ≤ v.num := Rat.num_nonneg.mpr hv
  have : ((v.num.toNat : ℕ) : ℤ) = v.num := Int.toNat_of_nonneg h
  exact_mod_cast this

lemma v_eq_frac {v : ℚ} (hv : 0 ≤ v) : v = (v.num.toNat : ℚ) / (v.den : ℚ) := by
  rw [num_toNat_cast hv]
  exact (Rat.num_div_den v).symm

/-- Key integer bounds: k² ≤ v·s² < (k+1)². -/
lemma kOf_bounds {v : ℚ} (hv : 0 ≤ v) (s : ℕ) :
    ((kOf v s : ℚ)) ^ 2 ≤ v * (s : ℚ) ^ 2 ∧
    v * (s : ℚ) ^ 2 < ((kOf v s : ℚ) + 1) ^ 2 := by
  have hdpos : 0 < v.den := v.den_pos
  have hdq : (0 : ℚ) < (v.den : ℚ) := by exact_mod_cast hdpos
  have h1 : ((v.num.toNat * s * s) / v.den) * v.den ≤ v.num.toNat * s * s :=
    Nat.div_mul_le_self _ _
  have h2 : v.num.toNat * s * s < ((v.num.toNat * s * s) / v.den + 1) * v.den :=
    (Nat.lt_mul_div_succ _ hdpos).trans_eq (by ring)
  have hv' : v * (s : ℚ) ^ 2 = (v.num.toNat : ℚ) * (s : ℚ) * (s : ℚ) / (v.den : ℚ) := by
    conv_lhs => rw [v_eq_frac hv]
    ring
  have hqQ1 : (((v.num.toNat * s * s) / v.den : ℕ) : ℚ) * (v.den : ℚ)
      ≤ (v.num.toNat : ℚ) * (s : ℚ) * (s : ℚ) := by
    exact_mod_cast h1
  have hqQ2 : (v.num.toNat : ℚ) * (s : ℚ) * (s : ℚ)
      < ((((v.num.toNat * s * s) / v.den : ℕ) : ℚ) + 1) * (v.den : ℚ) := by
    exact_mod_cast h2
  set q := (v.num.toNat * s * s) / v.den with hq
  have hle : (q : ℚ) ≤ v * (s : ℚ) ^ 2 := by
    rw [hv', le_div_iff₀ hdq]; linarith
  have hlt : v * (s : ℚ) ^ 2 < (q : ℚ) + 1 := by
    rw [hv', div_lt_iff₀ hdq]; linarith
  -- integer bounds on k = Nat.sqrt q
  have hk1 : Nat.sqrt q * Nat.sqrt q ≤ q := Nat.sqrt_le q
  have hk2 : q < (Nat.sqrt q + 1) * (Nat.sqrt q + 1) := Nat.lt_succ_sqrt q
  have hk1Q : ((Nat.sqrt q : ℕ) : ℚ) * (Nat.sqrt q : ℚ) ≤ (q : ℚ) := by
    exact_mod_cast hk1
  have hk2Q : (q : ℚ) + 1 ≤ ((Nat.sqrt q : ℚ) + 1) * ((Nat.sqrt q : ℚ) + 1) := by
    have : q + 1 ≤ (Nat.sqrt q + 1) * (Nat.sqrt q + 1) := hk2
    exact_mod_cast this
  have hkdef : kOf v s = Nat.sqrt q := rfl
  rw [hkdef]
  constructor
  · nlinarith
  · nlinarith

/-! ### Real-valued enclosure -/

lemma le_sqrt_of_sq_le {a b : ℚ} (ha : 0 ≤ a) (h : a ^ 2 ≤ b) :
    (a : ℝ) ≤ Real.sqrt (b : ℝ) := by
  have h' : ((a : ℝ)) ^ 2 ≤ (b : ℝ) := by exact_mod_cast h
  have ha' : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  calc (a : ℝ) = Real.sqrt ((a : ℝ) ^ 2) := (Real.sqrt_sq ha').symm
    _ ≤ Real.sqrt (b : ℝ) := Real.sqrt_le_sqrt h'

lemma sqrt_le_of_le_sq {v b : ℚ} (hb : 0 ≤ b) (h : v ≤ b ^ 2) :
    Real.sqrt (v : ℝ) ≤ (b : ℝ) := by
  have h' : (v : ℝ) ≤ ((b : ℝ)) ^ 2 := by exact_mod_cast h
  have hb' : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  calc Real.sqrt (v : ℝ) ≤ Real.sqrt (((b : ℝ)) ^ 2) := Real.sqrt_le_sqrt h'
    _ = (b : ℝ) := Real.sqrt_sq hb'

/-- Certificate form: lo² ≤ v ≤ hi² with 0 ≤ lo and 0 ≤ hi gives lo ≤ √v ≤ hi.
    This is the lemma that lets `Cases.lean` check exported Python outputs. -/
lemma enclosure_of_sq {lo hi v : ℚ} (hlo : 0 ≤ lo) (h1 : lo ^ 2 ≤ v)
    (h2 : v ≤ hi ^ 2) (hhi : 0 ≤ hi) :
    (lo : ℝ) ≤ Real.sqrt (v : ℝ) ∧ Real.sqrt (v : ℝ) ≤ (hi : ℝ) :=
  ⟨le_sqrt_of_sq_le hlo h1, sqrt_le_of_le_sq hhi h2⟩

/-! ### The Python algorithm -/

lemma lower_nonneg (v : ℚ) (s : ℕ) : 0 ≤ lower v s := by
  unfold lower; positivity

lemma upper_nonneg {v : ℚ} (s : ℕ) : 0 ≤ upper v s := by
  unfold upper
  split_ifs
  · exact lower_nonneg v s
  · positivity

lemma lower_le_sqrt {v : ℚ} (hv : 0 ≤ v) (s : ℕ) (hs : 0 < s) :
    (lower v s : ℝ) ≤ Real.sqrt (v : ℝ) := by
  have hsQ : (0 : ℚ) < s := by exact_mod_cast hs
  have hb := (kOf_bounds hv s).1
  have key : (lower v s) ^ 2 ≤ v := by
    unfold lower
    rw [div_pow, div_le_iff₀ (pow_pos hsQ 2)]
    linarith
  exact le_sqrt_of_sq_le (lower_nonneg v s) key

lemma sqrt_le_upper {v : ℚ} (hv : 0 ≤ v) (s : ℕ) (hs : 0 < s) :
    Real.sqrt (v : ℝ) ≤ (upper v s : ℝ) := by
  have hsQ : (0 : ℚ) < s := by exact_mod_cast hs
  unfold upper
  split_ifs with heq
  · -- lower² = v, so √v = lower
    have hsqR : ((lower v s : ℚ) : ℝ) ^ 2 = (v : ℝ) := by
      exact_mod_cast (show lower v s ^ 2 = v by rw [sq]; exact heq)
    have hl : (0 : ℝ) ≤ ((lower v s : ℚ) : ℝ) := by exact_mod_cast lower_nonneg v s
    rw [← hsqR, Real.sqrt_sq hl]
  · apply sqrt_le_of_le_sq
    · positivity
    · have hb := (kOf_bounds hv s).2
      rw [div_pow, le_div_iff₀ (pow_pos hsQ 2)]
      linarith

lemma upper_sub_lower_le {v : ℚ} (s : ℕ) (hs : 0 < s) :
    upper v s - lower v s ≤ 1 / (s : ℚ) := by
  have hsQ : (0 : ℚ) < s := by exact_mod_cast hs
  unfold upper
  split_ifs
  · rw [sub_self]; positivity
  · unfold lower
    rw [← sub_div]
    apply le_of_eq
    congr 1
    ring

lemma upper_eq_lower_of_sq (v : ℚ) (s : ℕ) (h : lower v s * lower v s = v) :
    upper v s = lower v s := by
  unfold upper
  simp [h]

lemma exactRoot_sound {v : ℚ} (hv : 0 ≤ v) {r : ℚ} (h : exactRoot v = some r) :
    (r : ℝ) = Real.sqrt (v : ℝ) := by
  unfold exactRoot at h
  split_ifs at h with hc
  · obtain ⟨hn, hd⟩ := hc
    have hr : r = (Nat.sqrt v.num.toNat : ℚ) / (Nat.sqrt v.den : ℚ) :=
      (Option.some.inj h).symm
    have hsq : r ^ 2 = v := by
      have hn' : ((Nat.sqrt v.num.toNat : ℕ) : ℚ) ^ 2 = (v.num.toNat : ℚ) := by
        rw [sq]; exact_mod_cast hn
      have hd' : ((Nat.sqrt v.den : ℕ) : ℚ) ^ 2 = (v.den : ℚ) := by
        rw [sq]; exact_mod_cast hd
      rw [hr, div_pow, hn', hd']
      exact (v_eq_frac hv).symm
    have hr0 : 0 ≤ r := by rw [hr]; positivity
    have hsqR : ((r : ℝ)) ^ 2 = (v : ℝ) := by exact_mod_cast hsq
    have hr0R : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
    rw [← hsqR, Real.sqrt_sq hr0R]

/-- Python `MNE.sqrt` on [lo, hi] encloses √x for every x in [lo, hi]. -/
theorem pySqrt_enclosure {lo hi : ℚ} (hlo : 0 ≤ lo) (hlh : lo ≤ hi)
    (s : ℕ) (hs : 0 < s) (x : ℚ) (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    ((pySqrt lo hi s).1 : ℝ) ≤ Real.sqrt (x : ℝ) ∧
    Real.sqrt (x : ℝ) ≤ ((pySqrt lo hi s).2 : ℝ) := by
  have hxR1 : (lo : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hxR2 : (x : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hx2
  unfold pySqrt
  split_ifs with heq
  · -- lo = hi, so x = lo
    have hxeq : (x : ℝ) = (lo : ℝ) := by
      have : x = lo := le_antisymm (by rw [heq]; exact hx2) hx1
      rw [this]
    cases hE : exactRoot lo with
    | some r =>
      simp only [hE]
      have hr := exactRoot_sound hlo hE
      rw [hxeq, hr]
      exact ⟨le_rfl, le_rfl⟩
    | none =>
      simp only [hE]
      rw [hxeq]
      exact ⟨lower_le_sqrt hlo s hs, sqrt_le_upper hlo s hs⟩
  · constructor
    · exact le_trans (lower_le_sqrt hlo s hs) (Real.sqrt_le_sqrt hxR1)
    · exact le_trans (Real.sqrt_le_sqrt hxR2) (sqrt_le_upper (le_trans hlo hlh) s hs)

/-- What an exact-input certificate asserts: lo ≤ √v ≤ hi and hi - lo ≤ w. -/
def SqrtCert (lo hi v w : ℚ) : Prop :=
  (lo : ℝ) ≤ Real.sqrt (v : ℝ) ∧ Real.sqrt (v : ℝ) ≤ (hi : ℝ) ∧ hi - lo ≤ w

/-- What an interval certificate asserts: L ≤ √x ≤ U for every x in [a, b]. -/
def SqrtInterval (a b L U : ℚ) : Prop :=
  ∀ x : ℚ, a ≤ x → x ≤ b → (L : ℝ) ≤ Real.sqrt (x : ℝ) ∧ Real.sqrt (x : ℝ) ≤ (U : ℝ)

/-- Certificate for an exact input v: lo² ≤ v ≤ hi², 0 ≤ lo, 0 ≤ hi and
    hi - lo ≤ w give lo ≤ √v ≤ hi and the width bound, all at once. -/
lemma sqrt_cert {lo hi v w : ℚ} (hlo : 0 ≤ lo) (h1 : lo ^ 2 ≤ v) (h2 : v ≤ hi ^ 2)
    (hhi : 0 ≤ hi) (hw : hi - lo ≤ w) :
    (lo : ℝ) ≤ Real.sqrt (v : ℝ) ∧ Real.sqrt (v : ℝ) ≤ (hi : ℝ) ∧ hi - lo ≤ w := by
  obtain ⟨a, b⟩ := enclosure_of_sq hlo h1 h2 hhi
  exact ⟨a, b, hw⟩

/-- Certificate for an interval input [a, b]: with 0 ≤ L, L² ≤ a and b ≤ U²,
    every x in [a, b] satisfies L ≤ √x ≤ U. This is the Python
    `MNE(interval).sqrt` enclosure, which returns (lower a, upper b). -/
theorem sqrt_interval_cert {a b L U x : ℚ} (hL : 0 ≤ L) (hLa : L ^ 2 ≤ a)
    (hbU : b ≤ U ^ 2) (hU : 0 ≤ U) (hx1 : a ≤ x) (hx2 : x ≤ b) :
    (L : ℝ) ≤ Real.sqrt (x : ℝ) ∧ Real.sqrt (x : ℝ) ≤ (U : ℝ) := by
  have h1 : (L : ℝ) ≤ Real.sqrt (a : ℝ) := le_sqrt_of_sq_le hL hLa
  have h2 : Real.sqrt (b : ℝ) ≤ (U : ℝ) := sqrt_le_of_le_sq hU hbU
  have hxa : (a : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hxb : (x : ℝ) ≤ (b : ℝ) := by exact_mod_cast hx2
  exact ⟨le_trans h1 (Real.sqrt_le_sqrt hxa), le_trans (Real.sqrt_le_sqrt hxb) h2⟩

end RRPF.Sqrt
