import Mathlib.Analysis.Complex.Basic

namespace Complex
variable {ι : Type*} {a b : ℝ}

lemma le_of_eq_sum_of_eq_sum_norm (f : ι → ℂ) (s : Finset ι) (ha₀ : 0 ≤ a) (ha : a = ∑ i ∈ s, f i)
    (hb : b = ∑ i ∈ s, (‖f i‖ : ℂ)) : a ≤ b := by
  norm_cast at hb; rw [← Complex.abs_of_nonneg ha₀, ha, hb]; exact norm_sum_le s f

end Complex
