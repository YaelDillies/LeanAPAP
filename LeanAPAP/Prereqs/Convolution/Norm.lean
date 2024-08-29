import Mathlib.Data.Real.StarOrdered
import LeanAPAP.Prereqs.Convolution.Discrete.Defs
import LeanAPAP.Prereqs.LpNorm.Discrete.Basic

/-!
# Norm of a convolution

This file characterises the L1-norm of the convolution of two functions and proves the Young
convolution inequality.
-/

open Finset Function Real
open scoped ComplexConjugate ENNReal NNReal Pointwise

variable {α β : Type*} [Fintype α] [DecidableEq α] [AddCommGroup α]

section RCLike
variable [RCLike β]

@[simp] lemma lpNorm_trivChar (p : ℝ≥0∞) : ‖(trivChar : α → β)‖_[p] = 1 := by
  obtain _ | p := p
  · simp only [ENNReal.none_eq_top, linftyNorm_eq_ciSup, trivChar_apply, apply_ite, norm_one,
      norm_zero]
    exact IsLUB.ciSup_eq ⟨by aesop (add simp mem_upperBounds), fun x hx ↦ hx ⟨0, if_pos rfl⟩⟩
  obtain rfl | hp := eq_or_ne p 0
  · simp [l0Norm_eq_card]
  · simp [lpNorm_eq_sum hp, apply_ite, hp]

lemma conv_eq_l2Inner (f g : α → β) (a : α) : (f ∗ g) a = ⟪conj f, τ a fun x ↦ g (-x)⟫_[β] := by
  simp [l2Inner_eq_sum, conv_eq_sum_sub', map_sum]

lemma dconv_eq_l2Inner (f g : α → β) (a : α) : (f ○ g) a = conj ⟪f, τ a g⟫_[β] := by
  simp [l2Inner_eq_sum, dconv_eq_sum_sub', map_sum]

lemma l2Inner_dconv (f g h : α → β) : ⟪f, g ○ h⟫_[β] = ⟪conj g, conj f ∗ conj h⟫_[β] := by
  calc
    _ = ∑ b, ∑ a, g a * conj (h b) * conj (f (a - b)) := by
      simp_rw [l2Inner, mul_comm _ ((_ ○ _) _), sum_dconv_mul]; exact sum_comm
    _ = ∑ b, ∑ a, conj (f a) * conj (h b) * g (a + b) := by
      simp_rw [← Fintype.sum_prod_type']
      exact Fintype.sum_equiv ((Equiv.refl _).prodShear Equiv.subRight) _ _
        (by simp [mul_rotate, mul_right_comm])
    _ = _ := by
      simp_rw [l2Inner, mul_comm _ ((_ ∗ _) _), sum_conv_mul, Pi.conj_apply, RCLike.conj_conj]
      exact sum_comm

lemma l2Inner_conv (f g h : α → β) : ⟪f, g ∗ h⟫_[β] = ⟪conj g, conj f ○ conj h⟫_[β] := by
  simp_rw [l2Inner_dconv, RCLike.conj_conj]

lemma dconv_l2Inner (f g h : α → β) : ⟪f ○ g, h⟫_[β] = ⟪conj h ∗ conj g, conj f⟫_[β] := by
  rw [l2Inner_anticomm, l2Inner_anticomm (_ ∗ _), conj_dconv, l2Inner_dconv]; simp

lemma conv_l2Inner (f g h : α → β) : ⟪f ∗ g, h⟫_[β] = ⟪conj h ○ conj g, conj f⟫_[β] := by
  rw [l2Inner_anticomm, l2Inner_anticomm (_ ○ _), conj_conv, l2Inner_conv]; simp

-- TODO: This proof would feel much less painful if we had `ℝ≥0`-valued Lp-norms.
/-- A special case of **Young's convolution inequality**. -/
lemma lpNorm_conv_le {p : ℝ≥0} (hp : 1 ≤ p) (f g : α → β) : ‖f ∗ g‖_[p] ≤ ‖f‖_[p] * ‖g‖_[1] := by
  obtain rfl | hp := hp.eq_or_lt
  · simp_rw [ENNReal.coe_one, l1Norm_eq_sum, sum_mul_sum, conv_eq_sum_sub']
    calc
      ∑ x, ‖∑ y, f y * g (x - y)‖ ≤ ∑ x, ∑ y, ‖f y * g (x - y)‖ :=
        sum_le_sum fun x _ ↦ norm_sum_le _ _
      _ = _ := ?_
    rw [sum_comm]
    simp_rw [norm_mul]
    exact sum_congr rfl fun x _ ↦ Fintype.sum_equiv (Equiv.subRight x) _ _ fun _ ↦ rfl
  have hp₀ := zero_lt_one.trans hp
  rw [← rpow_le_rpow_iff _ (mul_nonneg _ _) hp₀, mul_rpow]
  any_goals exact lpNorm_nonneg
  dsimp
  simp_rw [lpNorm_rpow_eq_sum hp₀.ne', conv_eq_sum_sub']
  have hpconj : (p : ℝ).IsConjExponent (1 - (p : ℝ)⁻¹)⁻¹ :=
    ⟨hp, by simp_rw [inv_inv, add_sub_cancel]⟩
  have (x) : ‖∑ y, f y * g (x - y)‖ ^ (p : ℝ) ≤
      (∑ y, ‖f y‖ ^ (p : ℝ) * ‖g (x - y)‖) * (∑ y, ‖g (x - y)‖) ^ (p - 1 : ℝ) := by
    rw [← le_rpow_inv_iff_of_pos (norm_nonneg _), mul_rpow, ← rpow_mul, sub_one_mul,
      mul_inv_cancel₀]
    any_goals positivity
    calc
      _ ≤ ∑ y, ‖f y * g (x - y)‖ := norm_sum_le _ _
      _ = ∑ y, ‖f y‖ * ‖g (x - y)‖ ^ (p : ℝ)⁻¹ * ‖g (x - y)‖ ^ (1 - (p : ℝ)⁻¹) := ?_
      _ ≤ _ := inner_le_Lp_mul_Lq _ _ _ hpconj
      _ = _ := ?_
    · congr with t
      rw [norm_mul, mul_assoc, ← rpow_add' (norm_nonneg _), add_sub_cancel, rpow_one]
      simp
    · have : 1 - (p : ℝ)⁻¹ ≠ 0 := sub_ne_zero.2 (inv_ne_one.2 $ NNReal.coe_ne_one.2 hp.ne').symm
      simp only [abs_mul, abs_rpow_of_nonneg, mul_rpow, rpow_nonneg, hp₀.ne', this,
        abs_norm, norm_nonneg, rpow_inv_rpow, Ne, NNReal.coe_eq_zero, not_false_iff, one_div,
        rpow_rpow_inv, div_inv_eq_mul, one_mul]
  calc
    ∑ x, ‖∑ y, f y * g (x - y)‖ ^ (p : ℝ) ≤
        ∑ x, (∑ y, ‖f y‖ ^ (p : ℝ) * ‖g (x - y)‖) * (∑ y, ‖g (x - y)‖) ^ (p - 1 : ℝ) :=
      sum_le_sum fun i _ ↦ this _
    _ = _ := ?_
  have hg : ∀ x, ∑ y, ‖g (x - y)‖ = ‖g‖_[1] := by
    simp_rw [l1Norm_eq_sum]
    exact fun x ↦ Fintype.sum_equiv (Equiv.subLeft _) _ _ fun _ ↦ rfl
  have hg' : ∀ y, ∑ x, ‖g (x - y)‖ = ‖g‖_[1] := by
    simp_rw [l1Norm_eq_sum]
    exact fun x ↦ Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl
  simp_rw [hg]
  rw [← sum_mul, sum_comm]
  simp_rw [← mul_sum, hg']
  rw [← sum_mul, mul_assoc, ← rpow_one_add' lpNorm_nonneg, add_sub_cancel]
  · rw [add_sub_cancel]
    positivity

/-- A special case of **Young's convolution inequality**. -/
lemma lpNorm_dconv_le {p : ℝ≥0} (hp : 1 ≤ p) (f g : α → β) : ‖f ○ g‖_[p] ≤ ‖f‖_[p] * ‖g‖_[1] := by
  simpa only [conv_conjneg, lpNorm_conjneg] using lpNorm_conv_le hp f (conjneg g)

end RCLike

section Real
variable {f g : α → ℝ} {n : ℕ}

--TODO: Include `f : α → ℂ`
lemma l1Norm_conv (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f ∗ g‖_[1] = ‖f‖_[1] * ‖g‖_[1] := by
  have : ∀ x, 0 ≤ ∑ y, f y * g (x - y) := fun x ↦ sum_nonneg fun y _ ↦ mul_nonneg (hf _) (hg _)
  simp only [l1Norm_eq_sum, ← sum_conv, conv_eq_sum_sub', norm_of_nonneg (this _),
    norm_of_nonneg (hf _), norm_of_nonneg (hg _)]

lemma l1Norm_dconv (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f ○ g‖_[1] = ‖f‖_[1] * ‖g‖_[1] := by
  simpa using l1Norm_conv hf (conjneg_nonneg.2 hg)

end Real
