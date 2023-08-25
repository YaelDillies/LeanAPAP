import Mathbin.Analysis.Complex.Circle
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Basic
import Project.Mathlib.NumberTheory.LegendreSymbol.AddChar.Basic

#align_import mathlib.analysis.complex.circle

/-!
## TODO

Rename
* `exp_map_circle` → `circle.exp`
* `coe_inv_circle_eq_conj` → `circle.coe_inv_eq_conj`
* `coe_div_circle` → `circle.coe_div` + `norm_cast`
-/


attribute [norm_cast] coe_div_circle

open AddChar Real

open scoped ComplexConjugate Real

namespace circle

variable {r : ℝ}

@[simp, norm_cast]
theorem coe_exp (r : ℝ) : ↑(expMapCircle r) = Complex.exp (r * Complex.I) :=
  rfl

theorem exp_int_hMul_two_pi (n : ℤ) : expMapCircle (n * (2 * π)) = 1 :=
  Subtype.ext <| by simpa [mul_assoc] using Complex.exp_int_mul_two_pi_mul_I n

theorem exp_two_pi_hMul_int (n : ℤ) : expMapCircle (2 * π * n) = 1 := by
  simpa only [mul_comm] using exp_int_mul_two_pi n

theorem exp_two_pi : expMapCircle (2 * π) = 1 := by simpa using exp_int_mul_two_pi 1

theorem exp_eq_one : expMapCircle r = 1 ↔ ∃ n : ℤ, r = n * (2 * π) := by
  simp [Subtype.ext_iff, Complex.exp_eq_one_iff, ← mul_assoc, Complex.I_ne_zero, ←
    Complex.ofReal_inj]

noncomputable def e : AddChar ℝ circle :=
  AddChar.toMonoidHom'.symm
    { toFun := fun r => expMapCircle (2 * π * r.toAdd)
      map_one' := by simp
      map_mul' := by simp [mul_add, Complex.exp_add] }

theorem e_apply (r : ℝ) : e r = expMapCircle (2 * π * r) :=
  rfl

@[simp, norm_cast]
theorem coe_e (r : ℝ) : ↑(e r) = Complex.exp ((2 * π * r : ℝ) * Complex.I) :=
  rfl

@[simp]
theorem e_int (z : ℤ) : e z = 1 :=
  exp_two_pi_hMul_int _

@[simp]
theorem e_one : e 1 = 1 := by simpa using e_int 1

@[simp]
theorem e_add_int {z : ℤ} : e (r + z) = e r := by rw [map_add_mul, e_int, mul_one]

@[simp]
theorem e_sub_int {z : ℤ} : e (r - z) = e r := by rw [map_sub_eq_div, e_int, div_one]

@[simp]
theorem e_fract (r : ℝ) : e (Int.fract r) = e r := by rw [Int.fract, e_sub_int]

@[simp]
theorem e_mod_div {m : ℤ} {n : ℕ} : e ((m % n : ℤ) / n) = e (m / n) :=
  by
  obtain hn | hn := eq_or_ne (n : ℝ) 0
  · rw [hn, div_zero, div_zero]
  ·
    rw [Int.mod_def, Int.cast_sub, sub_div, Int.cast_mul, Int.cast_ofNat, mul_div_cancel_left _ hn,
      e_sub_int]

theorem e_eq_one : e r = 1 ↔ ∃ n : ℤ, r = n := by
  simp [e_apply, exp_eq_one, mul_comm (2 * π), pi_ne_zero]

end circle

