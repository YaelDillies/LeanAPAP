import Mathlib.Analysis.Complex.Basic
import LeanAPAP.Mathlib.Data.IsROrC.Basic

open scoped ComplexConjugate

namespace Complex
variable {x : ℂ}

lemma norm_I : ‖I‖ = 1 := abs_I

lemma mul_conj' (x : ℂ) : x * conj x = (‖x‖ : ℂ) ^ 2 := IsROrC.mul_conj' _
lemma conj_mul' (x : ℂ) : conj x * x = (‖x‖ : ℂ) ^ 2 := IsROrC.conj_mul' _

lemma inv_eq_conj (hx : ‖x‖ = 1) : x⁻¹ = conj x := IsROrC.inv_eq_conj hx

--TODO: Do we rather want the map as an explicit definition?
lemma exists_norm_eq_mul_self (x : ℂ) : ∃ c, ‖c‖ = 1 ∧ ↑‖x‖ = c * x :=
  IsROrC.exists_norm_eq_mul_self _

lemma exists_norm_mul_eq_self (x : ℂ) : ∃ c, ‖c‖ = 1 ∧ c * ‖x‖ = x :=
  IsROrC.exists_norm_mul_eq_self _

@[simp] lemma conj_div (x y : ℂ) : conj (x / y) = conj x / conj y := IsROrC.conj_div _ _

end Complex
