import Mathlib.Analysis.MeanInequalities

open Finset
open scoped BigOperators

namespace Real
variable {ι : Type*} {f g : ι → ℝ}

/-- **Weighted Hölder inequality**. -/
lemma inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) (p : ℝ) (hp : 1 ≤ p) (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hf : ∀ i, 0 ≤ f i) :
    ∑ i in s, w i * f i ≤
      (∑ i in s, w i) ^ (1 - p⁻¹ : ℝ) * (∑ i in s, w i * f i ^ (p : ℝ)) ^ (p⁻¹ : ℝ) := by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  calc
    _ = ∑ i in s, w i ^ (1 - p⁻¹) * (w i ^ p⁻¹ * f i) := ?_
    _ ≤ (∑ i in s, (w i ^ (1 - p⁻¹)) ^ (1 - p⁻¹)⁻¹) ^ (1 / (1 - p⁻¹)⁻¹) *
          (∑ i in s, (w i ^ p⁻¹ * f i) ^ p) ^ (1 / p) := ?_
    _ = _ := ?_
  · congr with i
    rw [← mul_assoc, ← rpow_add' (hw _), sub_add_cancel, rpow_one]
    simp
  · refine inner_le_Lp_mul_Lq_of_nonneg _ (.symm ⟨hp, by simp⟩) ?_ ?_ <;>
      intros i _ <;> have := hw i <;> have := hf i <;> positivity
  · have hp₀ : p ≠ 0 := by positivity
    have hp₁ : 1 - p⁻¹ ≠ 0 := by simp [sub_eq_zero, hp.ne']
    simp [mul_rpow, div_inv_eq_mul, one_mul, one_div, hw, hf, rpow_nonneg, hp₀, hp₁]

end Real
