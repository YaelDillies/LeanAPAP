import prereqs.convolution.order
import prereqs.lp_norm

/-!
# Norm of a convolution

This file characterises the L1-norm of the convolution of two functions and proves the Young
convolution inequality.
-/

open finset function real
open_locale big_operators complex_conjugate nnreal pointwise

variables {α β : Type*} [fintype α] [decidable_eq α] [add_comm_group α]

section is_R_or_C
variables [is_R_or_C β]

lemma conv_eq_inner (f g : α → β) (a : α) : (f ∗ g) a = ⟪conj f, τ a (λ x, g (-x))⟫_[β] :=
by simp [L2inner_eq_sum, conv_eq_sum_sub', map_sum]

lemma dconv_eq_inner (f g : α → β) (a : α) : (f ○ g) a = conj ⟪f, τ a g⟫_[β] :=
by simp [L2inner_eq_sum, dconv_eq_sum_sub, map_sum]

-- TODO: This proof would feel much less painful if we had `ℝ≥0`-valued Lp-norms.
/-- A special case of **Young's convolution inequality**. -/
lemma Lpnorm_conv_le {p : ℝ≥0} (hp : 1 ≤ p) (f g : α → β) : ‖f ∗ g‖_[p] ≤ ‖f‖_[p] * ‖g‖_[1] :=
begin
  obtain rfl | hp := hp.eq_or_lt,
  { simp_rw [ennreal.coe_one, L1norm_eq_sum, sum_mul_sum, conv_eq_sum_sub'],
    calc
        ∑ x, ‖∑ y, f y * g (x - y)‖ ≤ ∑ x y, ‖f y * g (x - y)‖
          : sum_le_sum $ λ x _, norm_sum_le _ _
      ... = _ : _,
    rw sum_comm,
    simp_rw [norm_mul, sum_product],
    exact sum_congr rfl (λ x _, fintype.sum_equiv (equiv.sub_right x) _ _ $ λ _, rfl) },
  have hp₀ := zero_lt_one.trans hp,
  rw [←rpow_le_rpow_iff _ (mul_nonneg _ _) hp₀, mul_rpow],
  any_goals { exact Lpnorm_nonneg },
  simp_rw [Lpnorm_rpow_eq_sum hp₀.ne', conv_eq_sum_sub'],
  have hpconj : is_conjugate_exponent p (1 - p⁻¹)⁻¹ :=
    ⟨hp, by simp_rw [one_div, inv_inv, add_sub_cancel'_right]⟩,
  have : ∀ x, ‖∑ y, f y * g (x - y)‖ ^ (p : ℝ) ≤
    (∑ y, ‖f y‖ ^ (p : ℝ) * ‖g (x - y)‖) * (∑ y, ‖g (x - y)‖) ^ (p - 1 : ℝ),
  { intro x,
    rw [←le_rpow_inv_iff_of_pos (norm_nonneg _), mul_rpow, ←rpow_mul, sub_one_mul, mul_inv_cancel],
    rotate 1,
    { positivity },
    { exact sum_nonneg (λ _ _, norm_nonneg _) },
    { exact sum_nonneg (λ _ _, by positivity) },
    { exact rpow_nonneg (sum_nonneg $ λ _ _, norm_nonneg _) },
    { exact mul_nonneg (sum_nonneg $ λ _ _, by positivity)
        (rpow_nonneg $ sum_nonneg $ λ _ _, norm_nonneg _) },
    { positivity },
    calc
      _ ≤ ∑ y, ‖f y * g (x - y)‖ : norm_sum_le _ _
    ... = ∑ y, ‖f y‖ * ‖g (x - y)‖ ^ (p⁻¹ : ℝ) * ‖g (x - y)‖ ^ (1 - p⁻¹ : ℝ) : _
    ... ≤ _ : inner_le_Lp_mul_Lq _ _ _ hpconj
    ... = _ : _,
    { congr' with t,
      rw [norm_mul, mul_assoc, ←rpow_add' (norm_nonneg _), add_sub_cancel'_right, rpow_one],
      simp },
    { have : (1 - p⁻¹ : ℝ) ≠ 0 := sub_ne_zero.2 (inv_ne_one.2 $ by exact_mod_cast hp.ne').symm,
      simp only [abs_mul, abs_rpow_of_nonneg, mul_rpow, rpow_nonneg_of_nonneg, hp₀.ne', this,
        abs_norm, norm_nonneg, rpow_inv_rpow, ne.def, nnreal.coe_eq_zero, not_false_iff, one_div,
        rpow_rpow_inv, div_inv_eq_mul, one_mul] } },
  calc
    ∑ x, ‖∑ y, f y * g (x - y)‖ ^ (p : ℝ)
      ≤ ∑ x, (∑ y, ‖f y‖ ^ (p : ℝ) * ‖g (x - y)‖) * (∑ y, ‖g (x - y)‖) ^ (p - 1 : ℝ)
      : sum_le_sum $ λ i _, this _
  ... = _ : _,
  have hg : ∀ x, ∑ y, ‖g (x - y)‖ = ‖g‖_[1],
  { simp_rw L1norm_eq_sum,
    exact λ x, fintype.sum_equiv (equiv.sub_left _) _ _ (λ _, rfl) },
  have hg' : ∀ y, ∑ x, ‖g (x - y)‖ = ‖g‖_[1],
  { simp_rw L1norm_eq_sum,
    exact λ x, fintype.sum_equiv (equiv.sub_right _) _ _ (λ _, rfl) },
  simp_rw hg,
  rw [←sum_mul, sum_comm],
  simp_rw [←mul_sum, hg'],
  rw [←sum_mul, mul_assoc, ←rpow_one_add' Lpnorm_nonneg, add_sub_cancel'_right],
  { rw add_sub_cancel'_right,
    positivity }
end

/-- A special case of **Young's convolution inequality**. -/
lemma Lpnorm_dconv_le {p : ℝ≥0} (hp : 1 ≤ p) (f g : α → β) : ‖f ○ g‖_[p] ≤ ‖f‖_[p] * ‖g‖_[1] :=
by simpa only [conv_conjneg, Lpnorm_conjneg] using Lpnorm_conv_le hp f (conjneg g)

end is_R_or_C

section real
variables {f g : α → ℝ} {n : ℕ} --TODO: Include `f : α → ℂ`

lemma L1norm_conv (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f ∗ g‖_[1] = ‖f‖_[1] * ‖g‖_[1] :=
begin
  have : ∀ x, 0 ≤ ∑ y, f y * g (x - y) := λ x, sum_nonneg (λ y _, mul_nonneg (hf _) (hg _)),
  simp only [L1norm_eq_sum, ←sum_conv, conv_eq_sum_sub', norm_of_nonneg (this _),
    norm_of_nonneg (hf _), norm_of_nonneg (hg _)],
end

lemma L1norm_dconv (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f ○ g‖_[1] = ‖f‖_[1] * ‖g‖_[1] :=
by simpa using L1norm_conv hf (conjneg_nonneg.2 hg)

end real
