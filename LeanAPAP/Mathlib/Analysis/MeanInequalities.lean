import Project.Prereqs.LpNorm

#align_import mathlib.analysis.mean_inequalities

/-!
### TODO

These lemmas are currently proved using `Lpnorm`. The dependency should be reversed.
-/


open Finset

open scoped BigOperators NNReal

namespace Real

variable {ι : Type _} {f g : ι → ℝ}

-- TODO: `nnreal` version
/-- Square root version of the **Cauchy-Schwarz inequality**. -/
theorem sum_sqrt_hMul_sqrt_le (s : Finset ι) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i in s, sqrt (f i) * sqrt (g i) ≤ sqrt (∑ i in s, f i) * sqrt (∑ i in s, g i) := by
  simpa [← @sum_attach _ _ s, l2inner_eq_sum, L2norm_eq_sum, hf _, hg _] using
    l2inner_le_L2norm_hMul_L2norm (fun i : s => sqrt <| f i) fun i : s => sqrt <| g i

variable [Fintype ι]

--TODO: Generalise to `∑ x in s`
theorem weighted_hoelder (p : ℝ≥0) (hp₀ : p ≠ 0) (hp₁ : p ≤ 1) (f g : ι → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 ≤ g x) :
    ∑ x, f x * g x ≤ (∑ x, f x) ^ (1 - p : ℝ) * (∑ x, f x * g x ^ (p⁻¹ : ℝ)) ^ (p : ℝ) :=
  by
  obtain rfl | hp₁ := hp₁.eq_or_lt
  · simp
  calc
    _ = ⟪fun x => f x ^ (↑(1 - p) : ℝ), fun x => f x ^ (p : ℝ) * g x⟫_[ℝ] := _
    _ ≤ ‖fun x => f x ^ (↑(1 - p) : ℝ)‖_[↑(1 - p)⁻¹] * ‖fun x => f x ^ (p : ℝ) * g x‖_[↑p⁻¹] :=
      (l2inner_le_lpnorm_hMul_lpnorm
        (is_conjugate_exponent.symm
          ⟨NNReal.one_lt_coe.2 <| one_lt_inv hp₀.bot_lt hp₁, by
            simp [NNReal.coe_inv, NNReal.coe_sub hp₁.le]⟩)
        _ _)
    _ = _ := _
  · rw [l2inner_eq_sum]
    congr with x
    rw [conj_trivial, ← mul_assoc, NNReal.coe_sub hp₁.le, ← rpow_add' (hf _), sub_add_cancel,
      NNReal.coe_one, rpow_one]
    simp only [NNReal.coe_one, sub_add_cancel, Ne.def, one_ne_zero, not_false_iff]
  · rw [lpnorm_eq_sum (inv_ne_zero hp₀), lpnorm_eq_sum (inv_ne_zero (tsub_pos_of_lt hp₁).ne')]
    simp only [NNReal.coe_sub hp₁.le, norm_of_nonneg, rpow_nonneg, mul_rpow, rpow_rpow_inv,
      NNReal.coe_ne_zero.2, hp₀, sub_ne_zero.2 (NNReal.coe_ne_one.2 hp₁.ne).symm, hf _, hg _,
      NNReal.coe_inv, Ne.def, not_false_iff, inv_inv, norm_mul, NNReal.coe_one]

theorem weighted_hoelder' (p : ℝ≥0) (hp : 1 ≤ p) (f g : ι → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 ≤ g x) :
    ∑ x, f x * g x ≤ (∑ x, f x) ^ (1 - p⁻¹ : ℝ) * (∑ x, f x * g x ^ (p : ℝ)) ^ (p⁻¹ : ℝ) := by
  simpa using
    weighted_hoelder p⁻¹ (inv_ne_zero <| by rintro rfl <;> simpa using hp) (inv_le_one hp) _ _ hf hg

end Real

