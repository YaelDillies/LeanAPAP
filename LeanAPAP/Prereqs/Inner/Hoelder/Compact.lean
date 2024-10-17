import LeanAPAP.Prereqs.Inner.Hoelder.Discrete
import LeanAPAP.Prereqs.LpNorm.Compact

/-! # Inner product -/

open Finset hiding card
open Fintype (card)
open Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ENNReal NNReal NNRat

variable {ι κ 𝕜 : Type*} [Fintype ι]

namespace RCLike
variable [RCLike 𝕜] {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι] {f : ι → 𝕜}

@[simp] lemma wInner_cWeight_self (f : ι → 𝕜) :
    ⟪f, f⟫ₙ_[𝕜] = ((‖f‖ₙ_[2] : ℝ) : 𝕜) ^ 2 := by
  simp_rw [← algebraMap.coe_pow, ← NNReal.coe_pow]
  simp [cL2Norm_sq_eq_expect_nnnorm, wInner_cWeight_eq_expect, RCLike.conj_mul]

lemma cL1Norm_mul (f g : ι → 𝕜) : ‖f * g‖ₙ_[1] = ⟪fun i ↦ ‖f i‖, fun i ↦ ‖g i‖⟫ₙ_[ℝ] := by
  simp [wInner_cWeight_eq_expect, cL1Norm_eq_expect_nnnorm]

/-- **Cauchy-Schwarz inequality** -/
lemma wInner_cWeight_le_cL2Norm_mul_cL2Norm (f g : ι → ℝ) : ⟪f, g⟫ₙ_[ℝ] ≤ ‖f‖ₙ_[2] * ‖g‖ₙ_[2] := by
  simp only [wInner_cWeight_eq_smul_wInner_one, cL2Norm_eq_expect_nnnorm, ← NNReal.coe_mul, expect,
    NNReal.coe_nnqsmul, ← NNRat.cast_smul_eq_nnqsmul ℝ≥0, smul_eq_mul, ← NNReal.mul_rpow,
    mul_mul_mul_comm, ← sq]
  simp only [NNReal.mul_rpow, ← dL2Norm_eq_sum_nnnorm, card_univ]
  rw [← NNReal.rpow_two, NNReal.rpow_rpow_inv two_ne_zero, NNReal.smul_def, smul_eq_mul]
  push_cast
  gcongr
  exact wInner_one_le_dL2Norm_mul_dL2Norm _ _

end RCLike

/-! ### Hölder inequality -/

namespace MeasureTheory
section Real
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] {p q : ℝ≥0}
  {f g : α → ℝ}

lemma cL1Norm_mul_of_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f * g‖ₙ_[1] = ⟪f, g⟫ₙ_[ℝ] := by
  convert cL1Norm_mul f g using 2 <;> ext a <;> refine (norm_of_nonneg ?_).symm; exacts [hf _, hg _]

/-- **Hölder's inequality**, binary case. -/
lemma wInner_cWeight_le_cLpNorm_mul_cLpNorm (hpq : p.IsConjExponent q) (f g : α → ℝ) :
    ⟪f, g⟫ₙ_[ℝ] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by
  have hp := hpq.ne_zero
  have hq := hpq.symm.ne_zero
  norm_cast at hp hq
  rw [wInner_cWeight_eq_expect, expect_eq_sum_div_card, cLpNorm_eq_expect_nnnorm hp,
    cLpNorm_eq_expect_nnnorm hq, expect_eq_sum_div_card, expect_eq_sum_div_card,
    NNReal.div_rpow, NNReal.div_rpow, ← NNReal.coe_mul, div_mul_div_comm, ← NNReal.rpow_add',
    hpq.coe.inv_add_inv_conj, NNReal.rpow_one]
  push_cast
  gcongr
  rw [← dLpNorm_eq_sum_norm hp, ← dLpNorm_eq_sum_norm hq, ← wInner_one_eq_sum]
  exact wInner_one_le_dLpNorm_mul_dLpNorm hpq.coe_ennreal _ _
  · simp [hpq.coe.inv_add_inv_conj]

/-- **Hölder's inequality**, binary case. -/
lemma abs_wInner_cWeight_le_dLpNorm_mul_dLpNorm (hpq : p.IsConjExponent q) (f g : α → ℝ) :
    |⟪f, g⟫ₙ_[ℝ]| ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] :=
  (abs_wInner_le fun _ ↦ by dsimp; positivity).trans $
    (wInner_cWeight_le_cLpNorm_mul_cLpNorm hpq _ _).trans_eq $ by simp_rw [cLpNorm_abs]

end Real

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
  {p q : ℝ≥0} {f g : α → 𝕜}

lemma norm_wInner_cWeight_le (f g : α → 𝕜) :
    ‖⟪f, g⟫ₙ_[𝕜]‖₊ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫ₙ_[ℝ] := by
  simpa [wInner_cWeight_eq_expect, norm_mul]
    using norm_expect_le (K := ℝ) (f := fun i ↦ conj (f i) * g i)

/-- **Hölder's inequality**, binary case. -/
lemma nnnorm_wInner_cWeight_le_dLpNorm_mul_dLpNorm (hpq : p.IsConjExponent q) (f g : α → 𝕜) :
    ‖⟪f, g⟫ₙ_[𝕜]‖₊ ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] :=
  calc
    _ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫ₙ_[ℝ] := norm_wInner_cWeight_le _ _
    _ ≤ ‖fun a ↦ ‖f a‖‖ₙ_[p] * ‖fun a ↦ ‖g a‖‖ₙ_[q] := wInner_cWeight_le_cLpNorm_mul_cLpNorm hpq _ _
    _ = ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by simp_rw [cLpNorm_norm]

/-- **Hölder's inequality**, binary case. -/
lemma cLpNorm_mul_le (hp : p ≠ 0) (hq : q ≠ 0) (r : ℝ≥0) (hpqr : p⁻¹ + q⁻¹ = r⁻¹) (f g : α → 𝕜) :
    ‖f * g‖ₙ_[r] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by
  have hr : r ≠ 0 := by
    rintro rfl
    simp [hp] at hpqr
  have : (‖(f * g) ·‖ ^ (r : ℝ)) = (‖f ·‖ ^ (r : ℝ)) * (‖g ·‖ ^ (r : ℝ)) := by
    ext; simp [mul_rpow, abs_mul]
  rw [cLpNorm_eq_cL1Norm_rpow, NNReal.rpow_inv_le_iff_of_pos, this, ← NNReal.coe_le_coe]
  push_cast
  rw [cL1Norm_mul_of_nonneg, mul_rpow, ← NNReal.coe_rpow, ← NNReal.coe_rpow, cLpNorm_rpow',
    cLpNorm_rpow', ← ENNReal.coe_div, ← ENNReal.coe_div]
  refine wInner_cWeight_le_cLpNorm_mul_cLpNorm ⟨?_, ?_⟩ _ _
  · norm_cast
    rw [div_eq_mul_inv, ← hpqr, mul_add, mul_inv_cancel₀ hp]
    exact lt_add_of_pos_right _ (by positivity)
  · norm_cast
    simp [div_eq_mul_inv, hpqr, ← mul_add, hr]
  any_goals intro a; dsimp
  all_goals positivity

/-- **Hölder's inequality**, binary case. -/
lemma cL1Norm_mul_le (hpq : p.IsConjExponent q) (f g : α → 𝕜) :
    ‖f * g‖ₙ_[1] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] :=
  cLpNorm_mul_le (mod_cast hpq.ne_zero) (mod_cast hpq.symm.ne_zero) _
    (by simpa using hpq.inv_add_inv_conj) _ _

/-- **Hölder's inequality**, finitary case. -/
lemma cLpNorm_prod_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {p : ι → ℝ≥0} (hp : ∀ i, p i ≠ 0)
    (q : ℝ≥0) (hpq : ∑ i ∈ s, (p i)⁻¹ = q⁻¹) (f : ι → α → 𝕜) :
    ‖∏ i ∈ s, f i‖ₙ_[q] ≤ ∏ i ∈ s, ‖f i‖ₙ_[p i] := by
  induction' s using Finset.cons_induction with i s hi ih generalizing q
  · cases not_nonempty_empty hs
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp only [sum_cons, sum_empty, add_zero, inv_inj] at hpq
    simp [← hpq]
  simp_rw [prod_cons]
  rw [sum_cons, ← inv_inv (∑ _ ∈ _, _ : ℝ≥0)] at hpq
  refine (cLpNorm_mul_le (hp _) (inv_ne_zero (sum_pos (fun _ _ ↦ ?_) hs).ne') _ hpq _ _).trans
    (mul_le_mul_left' (ih hs _ (inv_inv _).symm) _)
  exact pos_iff_ne_zero.2 (inv_ne_zero $ hp _)

end Hoelder
end MeasureTheory
