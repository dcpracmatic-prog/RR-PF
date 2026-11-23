/-
  BoundedNum: aritmetica con representacion exacta o cota de error.

  Modelo: un valor `val : ℝ` y una cota `bound ≥ 0` con la semantica
  `isValid x t  :=  |t - x.val| ≤ x.bound`.

  Operaciones: add, sub, mul, div. Teoremas de validez (add, sub, mul,
  div), preservacion de exactitud (add, mul), monotonia (add).

  Origen: modelo de Arturo (archivo original), corregido para compilar.
  Cambios respecto al original:
  1. `by cli_romeo` -> `by simp` (la tactica no existe).
  2. `abs_add_three` no existe en Mathlib: se usan dos `abs_add`.
  3. `deriving DecidableEq` eliminado (ℝ no tiene DecidableEq).
  4. En `add_valid`, `by ring_nf` dentro de `|·|` -> `by congr 1; ring`.
  5. Anadido: `sub_valid`, `div` y `div_valid`, `div_exact`.
  Sin `sorry`. Ver lean/README.md para la compilacion.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Tactic

/-!
# BoundedNum - Aritmetica con cotas de error

Modelo de numeros con representacion exacta o cota de error propagable.
-/

open Classical

/-- Número con cota de error.
    `val` es la representación principal.
    `bound` es una cota superior del error absoluto.
    Semántica: |verdadero - val| ≤ bound. -/
structure BoundedNum where
  val   : ℝ
  bound : ℝ
  nonneg_bound : 0 ≤ bound

namespace BoundedNum

/-- Clase Exacta: cota cero. -/
def isExact (x : BoundedNum) : Prop :=
  x.bound = 0

/-- Construcción de un número exacto a partir de un racional. -/
def exact (q : ℚ) : BoundedNum :=
  { val := (q : ℝ)
    bound := 0
    nonneg_bound := le_rfl }

/-- Construcción de un número aproximado con cota explícita. -/
def approx (v : ℝ) (u : ℝ) (h : 0 ≤ u) : BoundedNum :=
  { val := v
    bound := u
    nonneg_bound := h }

/-- Semántica de validez de la cota. -/
def isValid (x : BoundedNum) (trueVal : ℝ) : Prop :=
  |trueVal - x.val| ≤ x.bound

/-! ### Operaciones -/

/-- Suma con propagación de cotas.
    Se añade un posible error de redondeo `ε` (por defecto 0). -/
def add (x y : BoundedNum) (ε : ℝ := 0) (hε : 0 ≤ ε := by simp) : BoundedNum :=
  { val := x.val + y.val
    bound := x.bound + y.bound + ε
    nonneg_bound := add_nonneg (add_nonneg x.nonneg_bound y.nonneg_bound) hε }

/-- Resta. -/
def sub (x y : BoundedNum) (ε : ℝ := 0) (hε : 0 ≤ ε := by simp) : BoundedNum :=
  add x (approx (-y.val) y.bound y.nonneg_bound) ε hε

/-- Producto con propagación clásica de cotas. -/
def mul (x y : BoundedNum) (ε : ℝ := 0) (hε : 0 ≤ ε := by simp) : BoundedNum :=
  { val := x.val * y.val
    bound := |x.val| * y.bound + |y.val| * x.bound + x.bound * y.bound + ε
    nonneg_bound := by
      have hA : 0 ≤ |x.val| * y.bound := mul_nonneg (abs_nonneg _) y.nonneg_bound
      have hB : 0 ≤ |y.val| * x.bound := mul_nonneg (abs_nonneg _) x.nonneg_bound
      have hC : 0 ≤ x.bound * y.bound := mul_nonneg x.nonneg_bound y.nonneg_bound
      exact add_nonneg (add_nonneg (add_nonneg hA hB) hC) hε }

/-! ### Propiedades fundamentales -/

/-- Proposición 5.1 (adaptada): validez de la cota de la suma. -/
theorem add_valid
    (x y : BoundedNum) (tx ty : ℝ)
    (hx : isValid x tx) (hy : isValid y ty)
    (ε : ℝ := 0) (hε : 0 ≤ ε := by simp) :
    isValid (add x y ε hε) (tx + ty) := by
  unfold isValid add
  simp only
  have h1 : |tx - x.val| ≤ x.bound := hx
  have h2 : |ty - y.val| ≤ y.bound := hy
  calc
    |(tx + ty) - (x.val + y.val)|
        = |(tx - x.val) + (ty - y.val)| := by congr 1; ring
    _ ≤ |tx - x.val| + |ty - y.val|     := abs_add _ _
    _ ≤ x.bound + y.bound               := add_le_add h1 h2
    _ ≤ x.bound + y.bound + ε           := le_add_of_nonneg_right hε

/-- Proposición 5.2 (adaptada): validez de la cota del producto. -/
theorem mul_valid
    (x y : BoundedNum) (tx ty : ℝ)
    (hx : isValid x tx) (hy : isValid y ty)
    (ε : ℝ := 0) (hε : 0 ≤ ε := by simp) :
    isValid (mul x y ε hε) (tx * ty) := by
  unfold isValid mul
  simp only
  set δx := tx - x.val with hδx
  set δy := ty - y.val with hδy
  have hδx_abs : |δx| ≤ x.bound := by simpa [hδx] using hx
  have hδy_abs : |δy| ≤ y.bound := by simpa [hδy] using hy
  have h_exp : tx * ty - x.val * y.val =
      x.val * δy + y.val * δx + δx * δy := by
    rw [hδx, hδy]; ring
  calc
    |tx * ty - x.val * y.val|
        = |x.val * δy + y.val * δx + δx * δy| := by rw [h_exp]
    _ ≤ |x.val * δy| + |y.val * δx| + |δx * δy| := by
        calc |x.val * δy + y.val * δx + δx * δy|
            ≤ |x.val * δy + y.val * δx| + |δx * δy| := abs_add _ _
          _ ≤ (|x.val * δy| + |y.val * δx|) + |δx * δy| :=
              add_le_add (abs_add _ _) le_rfl
          _ = |x.val * δy| + |y.val * δx| + |δx * δy| := by rw [add_assoc]
    _ ≤ |x.val| * |δy| + |y.val| * |δx| + |δx| * |δy| := by
        simp [abs_mul]
    _ ≤ |x.val| * y.bound + |y.val| * x.bound + x.bound * y.bound := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul_of_nonneg_left hδy_abs (abs_nonneg _)
          · exact mul_le_mul_of_nonneg_left hδx_abs (abs_nonneg _)
        · exact mul_le_mul hδx_abs hδy_abs (abs_nonneg _) x.nonneg_bound
    _ ≤ |x.val| * y.bound + |y.val| * x.bound + x.bound * y.bound + ε :=
        le_add_of_nonneg_right hε

/-- Preservación de la clase exacta bajo suma. -/
theorem add_exact
    (x y : BoundedNum) (hx : isExact x) (hy : isExact y) :
    isExact (add x y 0 (by simp)) := by
  have hx' : x.bound = 0 := hx
  have hy' : y.bound = 0 := hy
  unfold isExact add
  simp [hx', hy']

/-- Preservación de la clase exacta bajo producto. -/
theorem mul_exact
    (x y : BoundedNum) (hx : isExact x) (hy : isExact y) :
    isExact (mul x y 0 (by simp)) := by
  have hx' : x.bound = 0 := hx
  have hy' : y.bound = 0 := hy
  unfold isExact mul
  simp [hx', hy', abs_nonneg]

/-- Monotonía de las cotas respecto a las cotas de entrada (suma). -/
theorem add_mono_bound
    (x x' y y' : BoundedNum)
    (hx : x.bound ≤ x'.bound) (hy : y.bound ≤ y'.bound)
    (ε : ℝ := 0) (hε : 0 ≤ ε := by simp) :
    (add x y ε hε).bound ≤ (add x' y' ε hε).bound := by
  unfold add
  simp
  linarith

/-- División con propagación de cotas. Exige `y.bound < |y.val|`, es decir,
    que el intervalo de `y` no contenga al 0. La cota es
    (x.bound·|y.val| + |x.val|·y.bound) / (|y.val|·(|y.val| - y.bound)) + ε. -/
noncomputable def div (x y : BoundedNum) (h : y.bound < |y.val|) (ε : ℝ := 0) (hε : 0 ≤ ε := by simp) :
    BoundedNum :=
  { val := x.val / y.val
    bound := (x.bound * |y.val| + |x.val| * y.bound) / (|y.val| * (|y.val| - y.bound)) + ε
    nonneg_bound := by
      have hb : 0 ≤ y.bound := y.nonneg_bound
      have hpos : 0 < |y.val| - y.bound := sub_pos.mpr h
      have hD : 0 < |y.val| * (|y.val| - y.bound) := mul_pos (by linarith) hpos
      have hN : 0 ≤ x.bound * |y.val| + |x.val| * y.bound :=
        add_nonneg (mul_nonneg x.nonneg_bound (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) hb)
      exact add_nonneg (div_nonneg hN hD.le) hε }

/-! ### Propiedades fundamentales (continuacion) -/

/-- Validez de la cota de la resta. Sigue de `add_valid` y de que
    |(-ty) - (-y.val)| = |ty - y.val|. -/
theorem sub_valid
    (x y : BoundedNum) (tx ty : ℝ)
    (hx : isValid x tx) (hy : isValid y ty)
    (ε : ℝ := 0) (hε : 0 ≤ ε := by simp) :
    isValid (sub x y ε hε) (tx - ty) := by
  unfold sub
  rw [sub_eq_add_neg]
  refine add_valid x (approx (-y.val) y.bound y.nonneg_bound) tx (-ty) hx ?_ ε hε
  unfold isValid approx
  simp only
  rw [show -ty - -y.val = -(ty - y.val) by ring, abs_neg]
  exact hy

/-- Validez de la cota de la división. Hipótesis: el denominador tiene cota
    estrictamente menor que su valor absoluto (0 no está en su intervalo).
    Bajo esa hipótesis ty ≠ 0 se deduce de `hy`. -/
theorem div_valid
    (x y : BoundedNum) (tx ty : ℝ)
    (hx : isValid x tx) (hy : isValid y ty)
    (h : y.bound < |y.val|)
    (ε : ℝ := 0) (hε : 0 ≤ ε := by simp) :
    isValid (div x y h ε hε) (tx / ty) := by
  unfold isValid at hx hy
  unfold isValid div
  simp only
  have hb : 0 ≤ y.bound := y.nonneg_bound
  have hpos : 0 < |y.val| - y.bound := sub_pos.mpr h
  -- |ty| >= |y.val| - |ty - y.val| >= |y.val| - y.bound > 0
  have hty_lb : |y.val| - y.bound ≤ |ty| := by
    have h1 := abs_sub_abs_le_abs_sub y.val ty
    rw [abs_sub_comm y.val ty] at h1
    linarith
  have hty_pos : 0 < |ty| := by linarith
  have hty0 : ty ≠ 0 := abs_pos.mp hty_pos
  have hmy0 : y.val ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at h
    linarith
  have hmy_pos : 0 < |y.val| := by linarith
  -- identidad: tx/ty - mx/my = (tx*my - mx*ty) / (ty*my)
  rw [div_sub_div _ _ hty0 hmy0, abs_div]
  -- numerador: tx*my - ty*mx = (tx-mx)*my - mx*(ty-my)
  have hnum : tx * y.val - ty * x.val = (tx - x.val) * y.val - x.val * (ty - y.val) := by
    ring
  have hnum_bd : |tx * y.val - ty * x.val| ≤ x.bound * |y.val| + |x.val| * y.bound := by
    rw [hnum]
    have h1 := abs_sub ((tx - x.val) * y.val) (x.val * (ty - y.val))
    rw [abs_mul, abs_mul] at h1
    have h2 : |tx - x.val| * |y.val| ≤ x.bound * |y.val| :=
      mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    have h3 : |x.val| * |ty - y.val| ≤ |x.val| * y.bound :=
      mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    linarith
  have hden : |y.val| * (|y.val| - y.bound) ≤ |ty * y.val| := by
    rw [abs_mul, mul_comm (|y.val|) (|y.val| - y.bound)]
    exact mul_le_mul_of_nonneg_right hty_lb hmy_pos.le
  have hD : 0 < |y.val| * (|y.val| - y.bound) := mul_pos hmy_pos hpos
  have hN : 0 ≤ x.bound * |y.val| + |x.val| * y.bound :=
    add_nonneg (mul_nonneg x.nonneg_bound (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) hb)
  have key : |tx * y.val - ty * x.val| / |ty * y.val| ≤
      (x.bound * |y.val| + |x.val| * y.bound) / (|y.val| * (|y.val| - y.bound)) :=
    div_le_div₀ hN hnum_bd hD hden
  exact le_trans key (le_add_of_nonneg_right hε)

/-- Exactitud preservada por la división (con denominador no nulo). -/
theorem div_exact
    (x y : BoundedNum) (hx : isExact x) (hy : isExact y)
    (h : y.bound < |y.val|) :
    isExact (div x y h 0 (by simp)) := by
  have hx' : x.bound = 0 := hx
  have hy' : y.bound = 0 := hy
  unfold isExact div
  simp [hx', hy']


end BoundedNum

/-! ### Ejemplos de uso -/

-- Número exacto 1/3
def oneThird : BoundedNum := BoundedNum.exact (1/3)

-- Aproximación de √2 con cota 10⁻⁶.
-- Nota honesta: el valor guardado es `Real.sqrt 2` exacto, no un
-- decimal aproximado, asi que la cota es valida pero vacua.
-- Una aproximacion decimal real necesitaria probar la cota, y eso
-- no se hace aqui.
noncomputable def sqrt2Approx : BoundedNum :=
  BoundedNum.approx (Real.sqrt 2) 1e-6 (by norm_num)

-- Suma exacta
example : BoundedNum.isExact (BoundedNum.add oneThird oneThird) := by
  apply BoundedNum.add_exact
  · rfl
  · rfl

-- La cota de la suma de dos aproximaciones es válida
example (tx ty : ℝ)
    (hx : BoundedNum.isValid sqrt2Approx tx)
    (hy : BoundedNum.isValid sqrt2Approx ty) :
    BoundedNum.isValid (BoundedNum.add sqrt2Approx sqrt2Approx) (tx + ty) :=
  BoundedNum.add_valid sqrt2Approx sqrt2Approx tx ty hx hy
