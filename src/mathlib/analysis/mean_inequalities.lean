import prereqs.lp_norm

/-!
### TODO

These lemmas are currently proved using `Lpnorm`. The dependency should be reversed.
-/

open finset
open_locale big_operators nnreal

namespace real
variables {ι : Type*} {f g : ι → ℝ}

-- TODO: `nnreal` version
/-- Square root version of the **Cauchy-Schwarz inequality**. -/
lemma sum_sqrt_mul_sqrt_le (s : finset ι) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
  ∑ i in s, sqrt (f i) * sqrt (g i) ≤ sqrt (∑ i in s, f i) * sqrt (∑ i in s, g i) :=
by simpa [←@sum_attach _ _ s, L2inner_eq_sum, L2norm_eq_sum, hf _, hg _]
    using L2inner_le_L2norm_mul_L2norm (λ i : s, sqrt $ f i) (λ i : s, sqrt $ g i)

variables [fintype ι]

--TODO: Generalise to `∑ x in s`
lemma weighted_hoelder (p : ℝ≥0) (hp₀ : p ≠ 0) (hp₁ : p ≤ 1) (f g : ι → ℝ) (hf : ∀ x, 0 ≤ f x)
  (hg : ∀ x, 0 ≤ g x) :
  ∑ x, f x * g x ≤ (∑ x, f x) ^ (1 - p : ℝ) * (∑ x, f x * g x ^ (p⁻¹ : ℝ)) ^ (p : ℝ) :=
begin
  obtain rfl | hp₁ := hp₁.eq_or_lt,
  { simp },
  calc
      _ = ⟪λ x, f x ^ (↑(1 - p) : ℝ), λ x, f x ^ (p : ℝ) * g x⟫_[ℝ] : _
    ... ≤ ‖λ x, f x ^ (↑(1 - p) : ℝ)‖_[↑(1 - p)⁻¹] *
      ‖λ x, f x ^ (p : ℝ) * g x‖_[↑p⁻¹] : L2inner_le_Lpnorm_mul_Lpnorm
        (is_conjugate_exponent.symm ⟨nnreal.one_lt_coe.2 $ one_lt_inv hp₀.bot_lt hp₁,
        by simp [nnreal.coe_inv, nnreal.coe_sub hp₁.le]⟩) _ _
    ... = _ : _,
  { rw L2inner_eq_sum,
    congr' with x,
    rw [conj_trivial, ←mul_assoc, nnreal.coe_sub hp₁.le, ←rpow_add' (hf _), sub_add_cancel,
      nnreal.coe_one, rpow_one],
    simp only [nnreal.coe_one, sub_add_cancel, ne.def, one_ne_zero, not_false_iff] },
  { rw [Lpnorm_eq_sum (inv_ne_zero hp₀), Lpnorm_eq_sum (inv_ne_zero (tsub_pos_of_lt hp₁).ne')],
    simp only [nnreal.coe_sub hp₁.le, norm_of_nonneg, rpow_nonneg, mul_rpow, rpow_rpow_inv,
      nnreal.coe_ne_zero.2, hp₀, sub_ne_zero.2 (nnreal.coe_ne_one.2 hp₁.ne).symm, hf _, hg _,
      nnreal.coe_inv, ne.def, not_false_iff, inv_inv, norm_mul, nnreal.coe_one] }
end

lemma weighted_hoelder' (p : ℝ≥0) (hp : 1 ≤ p) (f g : ι → ℝ) (hf : ∀ x, 0 ≤ f x)
  (hg : ∀ x, 0 ≤ g x) :
  ∑ x, f x * g x ≤ (∑ x, f x) ^ (1 - p⁻¹ : ℝ) * (∑ x, f x * g x ^ (p : ℝ)) ^ (p⁻¹ : ℝ) :=
by simpa using
  weighted_hoelder p⁻¹ (inv_ne_zero $ by rintro rfl; simpa using hp) (inv_le_one hp) _ _ hf hg

end real
