import LeanAPAP.Prereqs.Discrete.LpNorm.Basic

/-!
### TODO

These lemmas are currently proved using `lpNorm`. The dependency should be reversed.
-/

open Finset

open scoped BigOperators NNReal

namespace Real
variable {ι : Type*} {f g : ι → ℝ}

-- TODO: `nnreal` version
/-- Square root version of the **Cauchy-Schwarz inequality**. -/
lemma sum_sqrt_mul_sqrt_le (s : Finset ι) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i in s, sqrt (f i) * sqrt (g i) ≤ sqrt (∑ i in s, f i) * sqrt (∑ i in s, g i) := by
  simpa [← sum_attach s, l2Inner_eq_sum, l2Norm_eq_sum, hf _, hg _] using
    l2Inner_le_l2Norm_mul_l2Norm (fun i : s ↦ sqrt $ f i) fun i : s ↦ sqrt $ g i

variable [Fintype ι]

--TODO: Generalise to `∑ x in s`
lemma weighted_hoelder (p : ℝ≥0) (hp₀ : p ≠ 0) (hp₁ : p ≤ 1) (f g : ι → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 ≤ g x) :
    ∑ x, f x * g x ≤ (∑ x, f x) ^ (1 - p : ℝ) * (∑ x, f x * g x ^ (p⁻¹ : ℝ)) ^ (p : ℝ) := by
  obtain rfl | hp₁ := hp₁.eq_or_lt
  · simp
  calc
    _ = ⟪fun x ↦ f x ^ (↑(1 - p) : ℝ), fun x ↦ f x ^ (p : ℝ) * g x⟫_[ℝ] := ?_
    _ ≤ ‖fun x ↦ f x ^ (↑(1 - p) : ℝ)‖_[↑(1 - p)⁻¹] * ‖fun x ↦ f x ^ (p : ℝ) * g x‖_[↑p⁻¹] :=
      l2Inner_le_lpNorm_mul_lpNorm (.one_sub_inv_inv hp₀ hp₁) _ _
    _ = _ := ?_
  · rw [l2Inner_eq_sum]
    congr with x
    rw [conj_trivial, ←mul_assoc, NNReal.coe_sub hp₁.le, ←rpow_add' (hf _), sub_add_cancel,
      NNReal.coe_one, rpow_one]
    simp only [NNReal.coe_one, sub_add_cancel, Ne.def, one_ne_zero, not_false_iff]
  · rw [lpNorm_eq_sum (inv_ne_zero hp₀), lpNorm_eq_sum (inv_ne_zero (tsub_pos_of_lt hp₁).ne')]
    simp only [NNReal.coe_sub hp₁.le, norm_of_nonneg, rpow_nonneg, mul_rpow, rpow_rpow_inv,
      NNReal.coe_ne_zero.2, hp₀, sub_ne_zero.2 (NNReal.coe_ne_one.2 hp₁.ne).symm, hf _, hg _,
      NNReal.coe_inv, Ne.def, not_false_iff, inv_inv, norm_mul, NNReal.coe_one]

lemma weighted_hoelder' (p : ℝ≥0) (hp : 1 ≤ p) (f g : ι → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 ≤ g x) :
    ∑ x, f x * g x ≤ (∑ x, f x) ^ (1 - p⁻¹ : ℝ) * (∑ x, f x * g x ^ (p : ℝ)) ^ (p⁻¹ : ℝ) := by
  simpa using
    weighted_hoelder p⁻¹ (inv_ne_zero $ by rintro rfl; simp at hp) (inv_le_one hp) _ _ hf hg

end Real
