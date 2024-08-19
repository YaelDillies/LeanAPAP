import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

open AddChar Multiplicative Real
open scoped ComplexConjugate Real

namespace Circle
variable {r s : ℝ}

noncomputable def e : AddChar ℝ Circle where
  toFun r := exp (2 * π * r)
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by simp [mul_add, Complex.exp_add]

lemma e_apply (r : ℝ) : e r = exp (2 * π * r) := rfl

@[simp, norm_cast] lemma coe_e (r : ℝ) : ↑(e r) = Complex.exp ((2 * π * r : ℝ) * Complex.I) := rfl

@[simp] lemma e_int (z : ℤ) : e z = 1 := exp_two_pi_mul_int _
@[simp] lemma e_one : e 1 = 1 := by simpa using e_int 1
@[simp] lemma e_add_int {z : ℤ} : e (r + z) = e r := by rw [map_add_eq_mul, e_int, mul_one]
@[simp] lemma e_sub_int {z : ℤ} : e (r - z) = e r := by rw [map_sub_eq_div, e_int, div_one]
@[simp] lemma e_fract (r : ℝ) : e (Int.fract r) = e r := by rw [Int.fract, e_sub_int]

@[simp] lemma e_mod_div {m : ℤ} {n : ℕ} : e ((m % n : ℤ) / n) = e (m / n) := by
  obtain hn | hn := eq_or_ne (n : ℝ) 0
  · rw [hn, div_zero, div_zero]
  · rw [Int.emod_def, Int.cast_sub, sub_div, Int.cast_mul, Int.cast_natCast,
      mul_div_cancel_left₀ _ hn, e_sub_int]

lemma e_eq_one : e r = 1 ↔ ∃ n : ℤ, r = n := by
  simp [e_apply, exp_eq_one, mul_comm (2 * π), pi_ne_zero]

lemma e_inj : e r = e s ↔ r ≡ s [PMOD 1] := by
  simp [AddCommGroup.ModEq, ← e_eq_one, div_eq_one, map_sub_eq_div, eq_comm (b := 1),
    eq_comm (a := e r)]

end Circle
