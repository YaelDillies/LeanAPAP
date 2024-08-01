import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Multiplicative Real
open scoped ComplexConjugate Real

namespace Circle
variable {r s : ℝ}

lemma exp_int_mul_two_pi (n : ℤ) : expMapCircle (n * (2 * π)) = 1 :=
  Subtype.ext $ by simpa [mul_assoc] using Complex.exp_int_mul_two_pi_mul_I n

lemma exp_two_pi_mul_int (n : ℤ) : expMapCircle (2 * π * n) = 1 := by
  simpa only [mul_comm] using exp_int_mul_two_pi n

lemma exp_two_pi : expMapCircle (2 * π) = 1 := by simp

lemma exp_eq_one : expMapCircle r = 1 ↔ ∃ n : ℤ, r = n * (2 * π) := by
  simp [Subtype.ext_iff, Complex.exp_eq_one_iff, ←mul_assoc, Complex.I_ne_zero, ←
    Complex.ofReal_inj]

end Circle
