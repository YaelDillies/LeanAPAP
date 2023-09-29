import Mathlib.Analysis.Complex.Basic
import LeanAPAP.Mathlib.Data.IsROrC.Basic

open scoped ComplexConjugate

namespace Complex

lemma norm_I : ‖I‖ = 1 := abs_I

lemma mul_conj' (x : ℂ) : x * conj x = (‖x‖ : ℂ) ^ 2 := IsROrC.mul_conj' _
lemma conj_mul' (x : ℂ) : conj x * x = (‖x‖ : ℂ) ^ 2 := IsROrC.conj_mul' _

end Complex
