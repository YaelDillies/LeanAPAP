import Mathlib.Analysis.SpecialFunctions.Complex.Log
import LeanAPAP.Mathlib.Analysis.Complex.Circle

open Function
open scoped Real

namespace Circle
variable {r s : ℝ} {x y : Circle}

lemma exp_int_mul_two_pi (n : ℤ) : exp (n * (2 * π)) = 1 :=
  ext $ by simpa [mul_assoc] using Complex.exp_int_mul_two_pi_mul_I n

lemma exp_two_pi_mul_int (n : ℤ) : exp (2 * π * n) = 1 := by
  simpa only [mul_comm] using exp_int_mul_two_pi n

lemma exp_eq_one : exp r = 1 ↔ ∃ n : ℤ, r = n * (2 * π) := by
  simp [Circle.ext_iff, Complex.exp_eq_one_iff, ← mul_assoc, Complex.I_ne_zero,
    ← Complex.ofReal_inj]

end Circle
