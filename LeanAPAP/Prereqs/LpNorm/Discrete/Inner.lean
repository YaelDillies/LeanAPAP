import Mathlib.Analysis.InnerProductSpace.PiL2
import LeanAPAP.Prereqs.LpNorm.Discrete.Defs

/-! # Inner product -/

open Finset Function Real
open scoped ComplexConjugate ENNReal NNReal NNRat

variable {ι R S : Type*} [Fintype ι]

namespace MeasureTheory
section CommSemiring
variable [CommSemiring R] [StarRing R] [DistribSMul S R]

/-- Inner product giving rise to the L2 norm. -/
def dL2Inner (f g : ι → R) : R := ∑ i, conj (f i) * g i

notation "⟪" f ", " g "⟫_[" S "]" => dL2Inner (R := S) f g

lemma dL2Inner_eq_sum (f g : ι → R) : ⟪f, g⟫_[R] = ∑ i, conj (f i) * g i := rfl

@[simp] lemma conj_dL2Inner (f g : ι → R) : conj ⟪f, g⟫_[R] = ⟪conj f, conj g⟫_[R] := by
  simp [dL2Inner_eq_sum, map_sum]

lemma dL2Inner_anticomm (f g : ι → R) : ⟪f, g⟫_[R] = ⟪conj g, conj f⟫_[R] := by
  simp [dL2Inner_eq_sum, map_sum, mul_comm]

@[simp] lemma dL2Inner_zero_left (g : ι → R) : ⟪0, g⟫_[R] = 0 := by simp [dL2Inner_eq_sum]
@[simp] lemma dL2Inner_zero_right (f : ι → R) : ⟪f, 0⟫_[R] = 0 := by simp [dL2Inner_eq_sum]

@[simp] lemma dL2Inner_of_isEmpty [IsEmpty ι] (f g : ι → R) : ⟪f, g⟫_[R] = 0 := by
  simp [Subsingleton.elim f 0]

@[simp] lemma dL2Inner_const_left (a : R) (f : ι → R) : ⟪const _ a, f⟫_[R] = conj a * ∑ x, f x := by
  simp only [dL2Inner_eq_sum, const_apply, mul_sum]

@[simp]
lemma dL2Inner_const_right (f : ι → R) (a : R) : ⟪f, const _ a⟫_[R] = (∑ x, conj (f x)) * a := by
  simp only [dL2Inner_eq_sum, const_apply, sum_mul]

lemma dL2Inner_add_left (f₁ f₂ g : ι → R) : ⟪f₁ + f₂, g⟫_[R] = ⟪f₁, g⟫_[R] + ⟪f₂, g⟫_[R] := by
  simp_rw [dL2Inner_eq_sum, Pi.add_apply, map_add, add_mul, sum_add_distrib]

lemma dL2Inner_add_right (f g₁ g₂ : ι → R) : ⟪f, g₁ + g₂⟫_[R] = ⟪f, g₁⟫_[R] + ⟪f, g₂⟫_[R] := by
  simp_rw [dL2Inner_eq_sum, Pi.add_apply, mul_add, sum_add_distrib]

lemma dL2Inner_smul_left [Star S] [StarModule S R] [IsScalarTower S R R] (c : S) (f g : ι → R) :
    ⟪c • f, g⟫_[R] = star c • ⟪f, g⟫_[R] := by
  simp only [dL2Inner_eq_sum, Pi.smul_apply, smul_mul_assoc, smul_sum, starRingEnd_apply, star_smul]

lemma dL2Inner_smul_right [Star S] [StarModule S R] [SMulCommClass S R R] (c : S) (f g : ι → R) :
    ⟪f, c • g⟫_[R] = c • ⟪f, g⟫_[R] := by
  simp only [dL2Inner_eq_sum, Pi.smul_apply, mul_smul_comm, smul_sum, starRingEnd_apply, star_smul]

lemma smul_dL2Inner_left [InvolutiveStar S] [StarModule S R] [IsScalarTower S R R] (c : S)
    (f g : ι → R) : c • ⟪f, g⟫_[R] = ⟪star c • f, g⟫_[R] := by rw [dL2Inner_smul_left, star_star]

end CommSemiring

section CommRing
variable [CommRing R] [StarRing R]

@[simp]
lemma dL2Inner_neg_left (f g : ι → R) : ⟪-f, g⟫_[R] = -⟪f, g⟫_[R] := by simp [dL2Inner_eq_sum]

@[simp]
lemma dL2Inner_neg_right (f g : ι → R) : ⟪f, -g⟫_[R] = -⟪f, g⟫_[R] := by simp [dL2Inner_eq_sum]

lemma dL2Inner_sub_left (f₁ f₂ g : ι → R) : ⟪f₁ - f₂, g⟫_[R] = ⟪f₁, g⟫_[R] - ⟪f₂, g⟫_[R] := by
  simp_rw [sub_eq_add_neg, dL2Inner_add_left, dL2Inner_neg_left]

lemma dL2Inner_sub_right (f g₁ g₂ : ι → R) : ⟪f, g₁ - g₂⟫_[R] = ⟪f, g₁⟫_[R] - ⟪f, g₂⟫_[R] := by
  simp_rw [sub_eq_add_neg, dL2Inner_add_right, dL2Inner_neg_right]

end CommRing

section OrderedCommSemiring
variable [OrderedCommSemiring R] [StarRing R] [StarOrderedRing R] {f g : ι → R}

lemma dL2Inner_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[R] :=
  sum_nonneg fun _ _ ↦ mul_nonneg (star_nonneg_iff.2 $ hf _) $ hg _

end OrderedCommSemiring

section LinearOrderedCommRing
variable [LinearOrderedCommRing R] [StarRing R] [TrivialStar R] {f g : ι → R}

--TODO: Can we remove the `TrivialStar` assumption?
lemma abs_dL2Inner_le_dL2Inner_abs : |⟪f, g⟫_[R]| ≤ ⟪|f|, |g|⟫_[R] :=
  (abs_sum_le_sum_abs _ _).trans_eq $
    sum_congr rfl fun i _ ↦ by simp only [abs_mul, conj_trivial, Pi.abs_apply]

end LinearOrderedCommRing

section RCLike
variable {κ : Type*} [RCLike R] {f : ι → R}

lemma dL2Inner_eq_inner (f g : ι → R) :
    ⟪f, g⟫_[R] = inner ((WithLp.equiv 2 _).symm f) ((WithLp.equiv 2 _).symm g) := rfl

lemma inner_eq_dL2Inner (f g : PiLp 2 fun _i : ι ↦ R) :
    inner f g = ⟪WithLp.equiv 2 _ f, WithLp.equiv 2 _ g⟫_[R] := rfl

@[simp] lemma dL2Inner_self {_ : MeasurableSpace ι} [DiscreteMeasurableSpace ι] (f : ι → R) :
    ⟪f, f⟫_[R] = ((‖f‖_[2] : ℝ) : R) ^ 2 := by
  simp_rw [← algebraMap.coe_pow, ← NNReal.coe_pow]
  simp [dL2Norm_sq_eq_sum_nnnorm, dL2Inner_eq_sum, RCLike.conj_mul]

lemma dL2Inner_self_of_norm_eq_one (hf : ∀ x, ‖f x‖ = 1) : ⟪f, f⟫_[R] = Fintype.card ι := by
  simp [-dL2Inner_self, dL2Inner_eq_sum, RCLike.conj_mul, hf, card_univ]

lemma linearIndependent_of_ne_zero_of_dL2Inner_eq_zero {v : κ → ι → R} (hz : ∀ k, v k ≠ 0)
    (ho : Pairwise fun k l ↦ ⟪v k, v l⟫_[R] = 0) : LinearIndependent R v := by
  simp_rw [dL2Inner_eq_inner] at ho
  have := linearIndependent_of_ne_zero_of_inner_eq_zero ?_ ho
  exacts [this, hz]

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

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function MeasureTheory

section OrderedCommSemiring
variable [OrderedCommSemiring R] [StarRing R] [StarOrderedRing R] {f g : ι → R}

private lemma dL2Inner_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[R] :=
  dL2Inner_nonneg hf.le hg

private lemma dL2Inner_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫_[R] :=
  dL2Inner_nonneg hf hg.le

private lemma dL2Inner_nonneg_of_pos_of_pos (hf : 0 < f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫_[R] :=
  dL2Inner_nonneg hf.le hg.le

end OrderedCommSemiring

/-- The `positivity` extension which identifies expressions of the form `⟪f, g⟫_[R]`. -/
@[positivity ⟪_, _⟫_[_]] def evalL2Inner : PositivityExt where eval {u R} _ _ e := do
  match e with
  | ~q(@dL2Inner $ι _ $instι $instring $inststar $f $g) =>
      let _p𝕜 ← synthInstanceQ q(OrderedCommSemiring $R)
      let _p𝕜 ← synthInstanceQ q(StarOrderedRing $R)
      assumeInstancesCommute
      match ← core q(inferInstance) q(inferInstance) f,
        ← core q(inferInstance) q(inferInstance) g with
      | .positive pf, .positive pg => return .nonnegative q(dL2Inner_nonneg_of_pos_of_pos $pf $pg)
      | .positive pf, .nonnegative pg =>
        return .nonnegative q(dL2Inner_nonneg_of_pos_of_nonneg $pf $pg)
      | .nonnegative pf, .positive pg =>
        return .nonnegative q(dL2Inner_nonneg_of_nonneg_of_pos $pf $pg)
      | .nonnegative pf, .nonnegative pg => return .nonnegative q(dL2Inner_nonneg $pf $pg)
      | _, _ => return .none
  | _ => throwError "not dL2Inner"

section OrderedCommSemiring
variable [OrderedCommSemiring R] [StarRing R] [StarOrderedRing R] {f g : ι → R}

example (hf : 0 < f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫_[R] := by positivity
example (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[R] := by positivity
example (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫_[R] := by positivity
example (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[R] := by positivity

end OrderedCommSemiring
end Mathlib.Meta.Positivity

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
