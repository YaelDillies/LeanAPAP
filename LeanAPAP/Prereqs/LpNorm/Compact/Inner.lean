import Mathlib.Analysis.InnerProductSpace.PiL2
import LeanAPAP.Mathlib.Algebra.Star.Rat
import LeanAPAP.Prereqs.Expect.Complex
import LeanAPAP.Prereqs.LpNorm.Compact.Defs
import LeanAPAP.Prereqs.LpNorm.Discrete.Inner

/-! # Inner product -/

open Finset hiding card
open Function Real
open Fintype (card)
open scoped BigOperators ComplexConjugate ENNReal NNReal NNRat

variable {ι R S : Type*} [Fintype ι]

namespace MeasureTheory
section CommSemiring
variable [CommSemiring R] [StarRing R] [Module ℚ≥0 R] [DistribSMul S R]

/-- Inner product giving rise to the L2 norm. -/
def cL2Inner (f g : ι → R) : R := 𝔼 i, conj (f i) * g i

notation "⟪" f ", " g "⟫ₙ_[" S "]" => cL2Inner (R := S) f g

lemma cL2Inner_eq_smul_dL2Inner (f g : ι → R) : ⟪f, g⟫ₙ_[R] = (card ι : ℚ≥0)⁻¹ • ⟪f, g⟫_[R]  := rfl

lemma cL2Inner_eq_expect (f g : ι → R) : ⟪f, g⟫ₙ_[R] = 𝔼 i, conj (f i) * g i := rfl

@[simp] lemma conj_cL2Inner (f g : ι → R) : conj ⟪f, g⟫ₙ_[R] = ⟪conj f, conj g⟫ₙ_[R] := by
  simp [cL2Inner_eq_expect, map_expect]
  exact Eq.trans (map_expect (starLinearEquiv ℚ≥0) _ _) (by simp [starRingEnd, starLinearEquiv])

lemma cL2Inner_anticomm (f g : ι → R) : ⟪f, g⟫ₙ_[R] = ⟪conj g, conj f⟫ₙ_[R] := by
  simp [cL2Inner_eq_expect, map_sum, mul_comm]

@[simp] lemma cL2Inner_zero_left (g : ι → R) : ⟪0, g⟫ₙ_[R] = 0 := by simp [cL2Inner_eq_expect]
@[simp] lemma cL2Inner_zero_right (f : ι → R) : ⟪f, 0⟫ₙ_[R] = 0 := by simp [cL2Inner_eq_expect]

@[simp] lemma cL2Inner_of_isEmpty [IsEmpty ι] (f g : ι → R) : ⟪f, g⟫ₙ_[R] = 0 := by
  simp [Subsingleton.elim f 0]

@[simp] lemma cL2Inner_const_left (a : R) (f : ι → R) :
    ⟪const _ a, f⟫ₙ_[R] = conj a * 𝔼 x, f x := by
 simp only [cL2Inner_eq_expect, const_apply, mul_expect]

@[simp]
lemma cL2Inner_const_right (f : ι → R) (a : R) : ⟪f, const _ a⟫ₙ_[R] = (𝔼 x, conj (f x)) * a := by
  simp only [cL2Inner_eq_expect, const_apply, expect_mul]

lemma cL2Inner_add_left (f₁ f₂ g : ι → R) : ⟪f₁ + f₂, g⟫ₙ_[R] = ⟪f₁, g⟫ₙ_[R] + ⟪f₂, g⟫ₙ_[R] := by
  simp_rw [cL2Inner_eq_expect, Pi.add_apply, map_add, add_mul, expect_add_distrib]

lemma cL2Inner_add_right (f g₁ g₂ : ι → R) : ⟪f, g₁ + g₂⟫ₙ_[R] = ⟪f, g₁⟫ₙ_[R] + ⟪f, g₂⟫ₙ_[R] := by
  simp_rw [cL2Inner_eq_expect, Pi.add_apply, mul_add, expect_add_distrib]

lemma cL2Inner_smul_left [Star S] [StarModule S R] [IsScalarTower S R R] (c : S) (f g : ι → R) :
    ⟪c • f, g⟫ₙ_[R] = star c • ⟪f, g⟫ₙ_[R] := by
  simp only [cL2Inner_eq_expect, Pi.smul_apply, smul_mul_assoc, smul_expect, starRingEnd_apply,
    star_smul]; sorry

lemma cL2Inner_smul_right [Star S] [StarModule S R] [SMulCommClass S R R] (c : S) (f g : ι → R) :
    ⟪f, c • g⟫ₙ_[R] = c • ⟪f, g⟫ₙ_[R] := by
  simp only [cL2Inner_eq_expect, Pi.smul_apply, mul_smul_comm, smul_expect, starRingEnd_apply,
    star_smul]; sorry

lemma smul_cL2Inner_left [InvolutiveStar S] [StarModule S R] [IsScalarTower S R R] (c : S)
    (f g : ι → R) : c • ⟪f, g⟫ₙ_[R] = ⟪star c • f, g⟫ₙ_[R] := by rw [cL2Inner_smul_left, star_star]

end CommSemiring

section CommRing
variable [CommRing R] [StarRing R] [Module ℚ≥0 R]

@[simp]
lemma cL2Inner_neg_left (f g : ι → R) : ⟪-f, g⟫ₙ_[R] = -⟪f, g⟫ₙ_[R] := by simp [cL2Inner_eq_expect]

@[simp]
lemma cL2Inner_neg_right (f g : ι → R) : ⟪f, -g⟫ₙ_[R] = -⟪f, g⟫ₙ_[R] := by simp [cL2Inner_eq_expect]

lemma cL2Inner_sub_left (f₁ f₂ g : ι → R) : ⟪f₁ - f₂, g⟫ₙ_[R] = ⟪f₁, g⟫ₙ_[R] - ⟪f₂, g⟫ₙ_[R] := by
  simp_rw [sub_eq_add_neg, cL2Inner_add_left, cL2Inner_neg_left]

lemma cL2Inner_sub_right (f g₁ g₂ : ι → R) : ⟪f, g₁ - g₂⟫ₙ_[R] = ⟪f, g₁⟫ₙ_[R] - ⟪f, g₂⟫ₙ_[R] := by
  simp_rw [sub_eq_add_neg, cL2Inner_add_right, cL2Inner_neg_right]

end CommRing

section OrderedCommSemiring
variable [OrderedCommSemiring R] [StarRing R] [StarOrderedRing R] [Module ℚ≥0 R]
  [PosSMulMono ℚ≥0 R] {f g : ι → R}

lemma cL2Inner_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫ₙ_[R] :=
  expect_nonneg fun _ _ ↦ mul_nonneg (star_nonneg_iff.2 $ hf _) $ hg _

end OrderedCommSemiring

section LinearOrderedCommRing
variable [LinearOrderedCommRing R] [StarRing R] [TrivialStar R] [Module ℚ≥0 R]
  [PosSMulMono ℚ≥0 R] {f g : ι → R}

--TODO: Can we remove the `TrivialStar` assumption?
lemma abs_cL2Inner_le_cL2Inner_abs : |⟪f, g⟫ₙ_[R]| ≤ ⟪|f|, |g|⟫ₙ_[R] :=
  (abs_expect_le_expect_abs _ _).trans_eq $
    expect_congr rfl fun i _ ↦ by simp only [abs_mul, conj_trivial, Pi.abs_apply]

end LinearOrderedCommRing

section RCLike
variable {κ : Type*} [RCLike R] {f : ι → R}

@[simp] lemma cL2Inner_self {_ : MeasurableSpace ι} [DiscreteMeasurableSpace ι] (f : ι → R) :
    ⟪f, f⟫ₙ_[R] = ((‖f‖ₙ_[2] : ℝ) : R) ^ 2 := by
  simp_rw [← algebraMap.coe_pow, ← NNReal.coe_pow]
  simp [cL2Norm_sq_eq_expect_nnnorm, cL2Inner_eq_expect, RCLike.conj_mul]

lemma cL2Inner_self_of_norm_eq_one [Nonempty ι] (hf : ∀ x, ‖f x‖ = 1) : ⟪f, f⟫ₙ_[R] = 1 := by
  simp [-cL2Inner_self, cL2Inner_eq_expect, RCLike.conj_mul, hf, card_univ]

lemma linearIndependent_of_ne_zero_of_cL2Inner_eq_zero {v : κ → ι → R} (hz : ∀ k, v k ≠ 0)
    (ho : Pairwise fun k l ↦ ⟪v k, v l⟫ₙ_[R] = 0) : LinearIndependent R v := by
  cases isEmpty_or_nonempty ι
  · have : IsEmpty κ := ⟨fun k ↦ hz k $ Subsingleton.elim _ _⟩
    exact linearIndependent_empty_type
  · exact linearIndependent_of_ne_zero_of_dL2Inner_eq_zero hz $ by
      simpa [cL2Inner_eq_smul_dL2Inner, ← NNRat.cast_smul_eq_nnqsmul R] using ho

variable {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι]

lemma cL1Norm_mul (f g : ι → R) : ‖f * g‖ₙ_[1] = ⟪fun i ↦ ‖f i‖, fun i ↦ ‖g i‖⟫ₙ_[ℝ] := by
  simp [cL2Inner_eq_expect, cL1Norm_eq_expect_nnnorm]

end RCLike

variable {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι]

/-- **Cauchy-Schwarz inequality** -/
lemma cL2Inner_le_cL2Norm_mul_cL2Norm (f g : ι → ℝ) : ⟪f, g⟫ₙ_[ℝ] ≤ ‖f‖ₙ_[2] * ‖g‖ₙ_[2] := by
  simp only [cL2Inner_eq_smul_dL2Inner, cL2Norm_eq_expect_nnnorm, ← NNReal.coe_mul, expect,
    NNReal.coe_nnqsmul, ← NNRat.cast_smul_eq_nnqsmul ℝ≥0, smul_eq_mul, ← NNReal.mul_rpow,
    mul_mul_mul_comm, ← sq]
  simp only [NNReal.mul_rpow, ← dL2Norm_eq_sum_nnnorm, card_univ]
  rw [← NNReal.rpow_two, NNReal.rpow_rpow_inv two_ne_zero, NNReal.smul_def, smul_eq_mul]
  push_cast
  gcongr
  exact dL2Inner_le_dL2Norm_mul_dL2Norm _ _

end MeasureTheory

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function MeasureTheory

section OrderedCommSemiring
variable [OrderedCommSemiring R] [StarRing R] [StarOrderedRing R] [Module ℚ≥0 R] [PosSMulMono ℚ≥0 R]
  {f g : ι → R}

private lemma cL2Inner_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫ₙ_[R] :=
  cL2Inner_nonneg hf.le hg

private lemma cL2Inner_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫ₙ_[R] :=
  cL2Inner_nonneg hf hg.le

private lemma cL2Inner_nonneg_of_pos_of_pos (hf : 0 < f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫ₙ_[R] :=
  cL2Inner_nonneg hf.le hg.le

end OrderedCommSemiring

/-- The `positivity` extension which identifies expressions of the form `⟪f, g⟫ₙ_[R]`. -/
@[positivity ⟪_, _⟫ₙ_[_]] def evalCL2Inner : PositivityExt where eval {u R} _ _ e := do
  match e with
  | ~q(@cL2Inner $ι _ $instι $instring $inster $inststar $f $g) =>
      let _p𝕜 ← synthInstanceQ q(OrderedCommSemiring $R)
      let _p𝕜 ← synthInstanceQ q(StarOrderedRing $R)
      let _p𝕜 ← synthInstanceQ q(Module ℚ≥0 $R)
      let _p𝕜 ← synthInstanceQ q(PosSMulMono ℚ≥0 $R)
      assumeInstancesCommute
      match ← core q(inferInstance) q(inferInstance) f,
        ← core q(inferInstance) q(inferInstance) g with
      | .positive pf, .positive pg => return .nonnegative q(cL2Inner_nonneg_of_pos_of_pos $pf $pg)
      | .positive pf, .nonnegative pg =>
        return .nonnegative q(cL2Inner_nonneg_of_pos_of_nonneg $pf $pg)
      | .nonnegative pf, .positive pg =>
        return .nonnegative q(cL2Inner_nonneg_of_nonneg_of_pos $pf $pg)
      | .nonnegative pf, .nonnegative pg => return .nonnegative q(cL2Inner_nonneg $pf $pg)
      | _, _ => return .none
  | _ => throwError "not cL2Inner"

section OrderedCommSemiring
variable [OrderedCommSemiring R] [StarRing R] [StarOrderedRing R] [Module ℚ≥0 R] [PosSMulMono ℚ≥0 R]
  {f g : ι → R}

example (hf : 0 < f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫ₙ_[R] := by positivity
example (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫ₙ_[R] := by positivity
example (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫ₙ_[R] := by positivity
example (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫ₙ_[R] := by positivity

end OrderedCommSemiring
end Mathlib.Meta.Positivity

/-! ### Hölder inequality -/

namespace MeasureTheory
section Real
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] {p q : ℝ≥0}
  {f g : α → ℝ}

lemma cL1Norm_mul_of_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f * g‖ₙ_[1] = ⟪f, g⟫ₙ_[ℝ] := by
  convert cL1Norm_mul f g using 2 <;> ext a <;> refine (norm_of_nonneg ?_).symm; exacts [hf _, hg _]

/-- **Hölder's inequality**, binary case. -/
lemma cL2Inner_le_cLpNorm_mul_cLpNorm (hpq : p.IsConjExponent q) (f g : α → ℝ) :
    ⟪f, g⟫ₙ_[ℝ] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by
  have hp := hpq.ne_zero
  have hq := hpq.symm.ne_zero
  norm_cast at hp hq
  rw [cL2Inner_eq_expect, expect_eq_sum_div_card, cLpNorm_eq_expect_nnnorm hp,
    cLpNorm_eq_expect_nnnorm hq, expect_eq_sum_div_card, expect_eq_sum_div_card,
    NNReal.div_rpow, NNReal.div_rpow, ← NNReal.coe_mul, div_mul_div_comm, ← NNReal.rpow_add',
    hpq.coe.inv_add_inv_conj, NNReal.rpow_one]
  push_cast
  gcongr
  rw [← dLpNorm_eq_sum_norm hp, ← dLpNorm_eq_sum_norm hq]
  exact dL2Inner_le_dLpNorm_mul_dLpNorm hpq _ _
  · simp [hpq.coe.inv_add_inv_conj]

/-- **Hölder's inequality**, binary case. -/
lemma abs_cL2Inner_le_dLpNorm_mul_dLpNorm (hpq : p.IsConjExponent q) (f g : α → ℝ) :
    |⟪f, g⟫ₙ_[ℝ]| ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] :=
  abs_cL2Inner_le_cL2Inner_abs.trans $
    (cL2Inner_le_cLpNorm_mul_cLpNorm hpq _ _).trans_eq $ by simp_rw [cLpNorm_abs]

end Real

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike R]
  {p q : ℝ≥0} {f g : α → R}

lemma norm_cL2Inner_le (f g : α → R) : ‖⟪f, g⟫ₙ_[R]‖₊ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫ₙ_[ℝ] :=
  (norm_expect_le (K := ℝ)).trans $ by simp [cL2Inner]

/-- **Hölder's inequality**, binary case. -/
lemma nnnorm_cL2Inner_le_dLpNorm_mul_dLpNorm (hpq : p.IsConjExponent q) (f g : α → R) :
    ‖⟪f, g⟫ₙ_[R]‖₊ ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] :=
  calc
    _ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫ₙ_[ℝ] := norm_cL2Inner_le _ _
    _ ≤ ‖fun a ↦ ‖f a‖‖ₙ_[p] * ‖fun a ↦ ‖g a‖‖ₙ_[q] := cL2Inner_le_cLpNorm_mul_cLpNorm hpq _ _
    _ = ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by simp_rw [cLpNorm_norm]

/-- **Hölder's inequality**, binary case. -/
lemma cLpNorm_mul_le (hp : p ≠ 0) (hq : q ≠ 0) (r : ℝ≥0) (hpqr : p⁻¹ + q⁻¹ = r⁻¹) (f g : α → R) :
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
  refine cL2Inner_le_cLpNorm_mul_cLpNorm ⟨?_, ?_⟩ _ _
  · norm_cast
    rw [div_eq_mul_inv, ← hpqr, mul_add, mul_inv_cancel₀ hp]
    exact lt_add_of_pos_right _ (by positivity)
  · norm_cast
    simp [div_eq_mul_inv, hpqr, ← mul_add, hr]
  any_goals intro a; dsimp
  all_goals positivity

/-- **Hölder's inequality**, binary case. -/
lemma cL1Norm_mul_le (hpq : p.IsConjExponent q) (f g : α → R) :
    ‖f * g‖ₙ_[1] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] :=
  cLpNorm_mul_le (mod_cast hpq.ne_zero) (mod_cast hpq.symm.ne_zero) _
    (by simpa using hpq.inv_add_inv_conj) _ _

/-- **Hölder's inequality**, finitary case. -/
lemma cLpNorm_prod_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {p : ι → ℝ≥0} (hp : ∀ i, p i ≠ 0)
    (q : ℝ≥0) (hpq : ∑ i ∈ s, (p i)⁻¹ = q⁻¹) (f : ι → α → R) :
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
