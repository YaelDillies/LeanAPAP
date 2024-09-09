import Mathlib.Analysis.MeanInequalities
import LeanAPAP.Prereqs.Expect.Basic

open Finset
open scoped BigOperators

namespace Real
variable {ι : Type*}

/-- **Weighted Hölder inequality**. -/
lemma compact_inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) {p : ℝ} (hp : 1 ≤ p) {w f : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) :
    𝔼 i ∈ s, w i * f i ≤ (𝔼 i ∈ s, w i) ^ (1 - p⁻¹) * (𝔼 i ∈ s, w i * f i ^ p) ^ p⁻¹ := by
  simp_rw [expect_eq_sum_div_card]
  rw [div_rpow, div_rpow, div_mul_div_comm, ← rpow_add', sub_add_cancel, rpow_one]
  gcongr
  exact inner_le_weight_mul_Lp_of_nonneg s hp _ _ hw hf
  any_goals simp
  all_goals exact sum_nonneg fun i _ ↦ by have := hw i; have := hf i; positivity

end Real
