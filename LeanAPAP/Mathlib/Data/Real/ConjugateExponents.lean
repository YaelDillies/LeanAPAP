import Mathlib.Data.Real.ConjugateExponents

/-!
## TODO

Change everything to using `x⁻¹` instead of `1 / x`.
-/

namespace Real.IsConjugateExponent
variable {p q : ℝ} (h : p.IsConjugateExponent q)

lemma inv_add_inv_conj' : p⁻¹ + q⁻¹ = 1 := by simpa only [one_div] using h.inv_add_inv_conj

lemma inv_add_inv_conj_nnreal' : p.toNNReal⁻¹ + q.toNNReal⁻¹ = 1 := by
  simpa only [one_div] using h.inv_add_inv_conj_nnreal

lemma inv_add_inv_conj_ennreal' : (ENNReal.ofReal p)⁻¹ + (ENNReal.ofReal q)⁻¹ = 1 := by
  simpa only [one_div] using h.inv_add_inv_conj_ennreal

end Real.IsConjugateExponent
