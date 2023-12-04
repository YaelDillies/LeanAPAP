import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import LeanAPAP.Mathlib.NumberTheory.LegendreSymbol.AddChar.Basic

/-!
## TODO

Rename
* `exp_map_circle` → `circle.exp`
* `coe_inv_circle_eq_conj` → `circle.coe_inv_eq_conj`
* `coe_div_circle` → `circle.coe_div` + `norm_cast`
-/

attribute [norm_cast] coe_div_circle

open AddChar Multiplicative Real
open scoped ComplexConjugate Real

namespace Circle
variable {r s : ℝ}

@[simp, norm_cast] lemma coe_exp (r : ℝ) : ↑(expMapCircle r) = Complex.exp (r * Complex.I) := rfl

lemma exp_int_mul_two_pi (n : ℤ) : expMapCircle (n * (2 * π)) = 1 :=
  Subtype.ext $ by simpa [mul_assoc] using Complex.exp_int_mul_two_pi_mul_I n

lemma exp_two_pi_mul_int (n : ℤ) : expMapCircle (2 * π * n) = 1 := by
  simpa only [mul_comm] using exp_int_mul_two_pi n

lemma exp_two_pi : expMapCircle (2 * π) = 1 := by simpa using exp_int_mul_two_pi 1

lemma exp_eq_one : expMapCircle r = 1 ↔ ∃ n : ℤ, r = n * (2 * π) := by
  simp [Subtype.ext_iff, Complex.exp_eq_one_iff, ←mul_assoc, Complex.I_ne_zero, ←
    Complex.ofReal_inj]

noncomputable def e : AddChar ℝ circle :=
  AddChar.toMonoidHom'.symm
    { toFun := fun r ↦ expMapCircle (2 * π * (toAdd r))
      map_one' := by simp
      map_mul' := by simp [mul_add, Complex.exp_add] }

lemma e_apply (r : ℝ) : e r = expMapCircle (2 * π * r) := rfl

@[simp, norm_cast] lemma coe_e (r : ℝ) : ↑(e r) = Complex.exp ((2 * π * r : ℝ) * Complex.I) := rfl

@[simp] lemma e_int (z : ℤ) : e z = 1 := exp_two_pi_mul_int _
@[simp] lemma e_one : e 1 = 1 := by simpa using e_int 1
@[simp] lemma e_add_int {z : ℤ} : e (r + z) = e r := by rw [map_add_mul, e_int, mul_one]
@[simp] lemma e_sub_int {z : ℤ} : e (r - z) = e r := by rw [map_sub_eq_div, e_int, div_one]
@[simp] lemma e_fract (r : ℝ) : e (Int.fract r) = e r := by rw [Int.fract, e_sub_int]

@[simp] lemma e_mod_div {m : ℤ} {n : ℕ} : e ((m % n : ℤ) / n) = e (m / n) := by
  obtain hn | hn := eq_or_ne (n : ℝ) 0
  · rw [hn, div_zero, div_zero]
  · rw [Int.emod_def, Int.cast_sub, sub_div, Int.cast_mul, Int.cast_ofNat, mul_div_cancel_left _ hn,
      e_sub_int]

lemma e_eq_one : e r = 1 ↔ ∃ n : ℤ, r = n := by
  simp [e_apply, exp_eq_one, mul_comm (2 * π), pi_ne_zero]

lemma e_inj : e r = e s ↔ r ≡ s [PMOD 1] := by
  simp [AddCommGroup.ModEq, ←e_eq_one, div_eq_one, map_sub_eq_div, eq_comm (b := 1),
    eq_comm (a := e r)]

end Circle
