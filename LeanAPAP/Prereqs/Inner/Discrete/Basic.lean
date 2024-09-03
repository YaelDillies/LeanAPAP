import Mathlib.Analysis.InnerProductSpace.PiL2
import LeanAPAP.Prereqs.LpNorm.Discrete.Defs
import LeanAPAP.Prereqs.Inner.Discrete.Defs

/-! # Inner product -/

open Finset Function Real
open scoped ComplexConjugate ENNReal NNReal NNRat

variable {ι R S : Type*} [Fintype ι]

namespace MeasureTheory

section RCLike
variable {κ : Type*} [RCLike R] {f : ι → R}

@[simp] lemma dL2Inner_self {_ : MeasurableSpace ι} [DiscreteMeasurableSpace ι] (f : ι → R) :
    ⟪f, f⟫_[R] = ((‖f‖_[2] : ℝ) : R) ^ 2 := by
  simp_rw [← algebraMap.coe_pow, ← NNReal.coe_pow]
  simp [dL2Norm_sq_eq_sum_nnnorm, dL2Inner_eq_sum, RCLike.conj_mul]

variable {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι]

lemma dL1Norm_mul (f g : ι → R) : ‖f * g‖_[1] = ⟪fun i ↦ ‖f i‖, fun i ↦ ‖g i‖⟫_[ℝ] := by
  simp [dL2Inner_eq_sum, dL1Norm_eq_sum_nnnorm]

end RCLike

variable {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι]

/-- **Cauchy-Schwarz inequality** -/
lemma dL2Inner_le_dL2Norm_mul_dL2Norm (f g : ι → ℝ) : ⟪f, g⟫_[ℝ] ≤ ‖f‖_[2] * ‖g‖_[2] := by
  simpa [dL2Norm_eq_sum_nnnorm, PiLp.norm_eq_of_L2, sqrt_eq_rpow]
    using real_inner_le_norm ((WithLp.equiv 2 _).symm f) _

end MeasureTheory

/-! ### Hölder inequality -/

namespace MeasureTheory
section Real
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] {p q : ℝ≥0}
  {f g : α → ℝ}

lemma dL1Norm_mul_of_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f * g‖_[1] = ⟪f, g⟫_[ℝ] := by
  convert dL1Norm_mul f g using 2 <;> ext a <;> refine (norm_of_nonneg ?_).symm; exacts [hf _, hg _]

/-- **Hölder's inequality**, binary case. -/
lemma dL2Inner_le_dLpNorm_mul_dLpNorm (hpq : p.IsConjExponent q) (f g : α → ℝ) :
    ⟪f, g⟫_[ℝ] ≤ ‖f‖_[p] * ‖g‖_[q] := by
  have hp := hpq.ne_zero
  have hq := hpq.symm.ne_zero
  norm_cast at hp hq
  simpa [dL2Inner_eq_sum, dLpNorm_eq_sum_nnnorm, *] using inner_le_Lp_mul_Lq _ f g hpq.coe

/-- **Hölder's inequality**, binary case. -/
lemma abs_dL2Inner_le_dLpNorm_mul_dLpNorm (hpq : p.IsConjExponent q) (f g : α → ℝ) :
    |⟪f, g⟫_[ℝ]| ≤ ‖f‖_[p] * ‖g‖_[q] :=
  abs_dL2Inner_le_dL2Inner_abs.trans $
    (dL2Inner_le_dLpNorm_mul_dLpNorm hpq _ _).trans_eq $ by simp_rw [dLpNorm_abs]

end Real

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike R]
  {p q : ℝ≥0} {f g : α → R}

lemma norm_dL2Inner_le (f g : α → R) : ‖⟪f, g⟫_[R]‖₊ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫_[ℝ] :=
  (norm_sum_le _ _).trans $ by simp [dL2Inner]

/-- **Hölder's inequality**, binary case. -/
lemma nnnorm_dL2Inner_le_dLpNorm_mul_dLpNorm (hpq : p.IsConjExponent q) (f g : α → R) :
    ‖⟪f, g⟫_[R]‖₊ ≤ ‖f‖_[p] * ‖g‖_[q] :=
  calc
    _ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫_[ℝ] := norm_dL2Inner_le _ _
    _ ≤ ‖fun a ↦ ‖f a‖‖_[p] * ‖fun a ↦ ‖g a‖‖_[q] := dL2Inner_le_dLpNorm_mul_dLpNorm hpq _ _
    _ = ‖f‖_[p] * ‖g‖_[q] := by simp_rw [dLpNorm_norm]

/-- **Hölder's inequality**, binary case. -/
lemma dLpNorm_mul_le (hp : p ≠ 0) (hq : q ≠ 0) (r : ℝ≥0) (hpqr : p⁻¹ + q⁻¹ = r⁻¹) (f g : α → R) :
    ‖f * g‖_[r] ≤ ‖f‖_[p] * ‖g‖_[q] := by
  have hr : r ≠ 0 := by
    rintro rfl
    simp [hp] at hpqr
  have : (‖(f * g) ·‖ ^ (r : ℝ)) = (‖f ·‖ ^ (r : ℝ)) * (‖g ·‖ ^ (r : ℝ)) := by
    ext; simp [mul_rpow, abs_mul]
  rw [dLpNorm_eq_dL1Norm_rpow, NNReal.rpow_inv_le_iff_of_pos, this, ← NNReal.coe_le_coe]
  push_cast
  rw [dL1Norm_mul_of_nonneg, mul_rpow, ← NNReal.coe_rpow, ← NNReal.coe_rpow, dLpNorm_rpow',
    dLpNorm_rpow', ← ENNReal.coe_div, ← ENNReal.coe_div]
  refine dL2Inner_le_dLpNorm_mul_dLpNorm ⟨?_, ?_⟩ _ _
  · norm_cast
    rw [div_eq_mul_inv, ← hpqr, mul_add, mul_inv_cancel₀ hp]
    exact lt_add_of_pos_right _ (by positivity)
  · norm_cast
    simp [div_eq_mul_inv, hpqr, ← mul_add, hr]
  any_goals intro a; dsimp
  all_goals positivity

/-- **Hölder's inequality**, binary case. -/
lemma dL1Norm_mul_le (hpq : p.IsConjExponent q) (f g : α → R) :
    ‖f * g‖_[1] ≤ ‖f‖_[p] * ‖g‖_[q] :=
  dLpNorm_mul_le (mod_cast hpq.ne_zero) (mod_cast hpq.symm.ne_zero) _
    (by simpa using hpq.inv_add_inv_conj) _ _

/-- **Hölder's inequality**, finitary case. -/
lemma dLpNorm_prod_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {p : ι → ℝ≥0} (hp : ∀ i, p i ≠ 0)
    (q : ℝ≥0) (hpq : ∑ i ∈ s, (p i)⁻¹ = q⁻¹) (f : ι → α → R) :
    ‖∏ i ∈ s, f i‖_[q] ≤ ∏ i ∈ s, ‖f i‖_[p i] := by
  induction' s using Finset.cons_induction with i s hi ih generalizing q
  · cases not_nonempty_empty hs
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp only [sum_cons, sum_empty, add_zero, inv_inj] at hpq
    simp [← hpq]
  simp_rw [prod_cons]
  rw [sum_cons, ← inv_inv (∑ _ ∈ _, _ : ℝ≥0)] at hpq
  refine (dLpNorm_mul_le (hp _) (inv_ne_zero (sum_pos (fun _ _ ↦ ?_) hs).ne') _ hpq _ _).trans
    (mul_le_mul_left' (ih hs _ (inv_inv _).symm) _)
  exact pos_iff_ne_zero.2 (inv_ne_zero $ hp _)

end Hoelder
end MeasureTheory
