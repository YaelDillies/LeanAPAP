import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import LeanAPAP.Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import LeanAPAP.Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import LeanAPAP.Mathlib.Algebra.Algebra.Basic

/-!
# Lp norms
-/

open Finset Function Real
open scoped ComplexConjugate ENNReal NNReal NNRat

variable {ι 𝕜 : Type*} [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

/-! ### Lp norm -/

namespace MeasureTheory
variable {E : Type*} [ NormedAddCommGroup E] {p q : ℝ≥0∞} {f g h : ι → E}

notation "‖" f "‖_[" p "]" => snorm f p Measure.count

lemma lpNorm_eq_sum' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (f : ι → E) :
    ‖f‖_[p] = (∑ i, ‖f i‖₊ ^ p.toReal : ℝ≥0∞) ^ p.toReal⁻¹ := by
  simp [snorm_eq_lintegral_rpow_nnnorm hp₀ hp, one_div, lintegral_count,
    tsum_eq_sum' (s := univ) (by simp), ENNReal.coe_rpow_of_nonneg]

lemma lpNorm_toNNReal_eq_sum {p : ℝ} (hp : 0 < p) (f : ι → E) :
    ‖f‖_[p.toNNReal] = (∑ i, ‖f i‖₊ ^ p : ℝ≥0∞) ^ p⁻¹ := by
  rw [lpNorm_eq_sum'] <;> simp [hp.ne', hp.le, hp]

lemma lpNorm_eq_sum {p : ℝ≥0} (hp : p ≠ 0) (f : ι → E) :
    ‖f‖_[p] = (∑ i, ‖f i‖₊ ^ (p : ℝ) : ℝ≥0∞) ^ (p⁻¹ : ℝ) := lpNorm_eq_sum' (by simpa using hp) (by simp) _

lemma lpNorm_rpow_eq_sum {p : ℝ≥0} (hp : p ≠ 0) (f : ι → E) :
    ‖f‖_[p] ^ (p : ℝ) = ∑ i, (‖f i‖₊ : ℝ≥0∞) ^ (p : ℝ) := by
  rw [lpNorm_eq_sum hp, ENNReal.rpow_inv_rpow (mod_cast hp)]

lemma lpNorm_pow_eq_sum {p : ℕ} (hp : p ≠ 0) (f : ι → E) :
    ‖f‖_[p] ^ p = ∑ i, (‖f i‖₊ : ℝ≥0∞) ^ p := by
  simpa using lpNorm_rpow_eq_sum (Nat.cast_ne_zero.2 hp) f

lemma l2Norm_sq_eq_sum (f : ι → E) : ‖f‖_[2] ^ 2 = ∑ i, ‖f i‖₊ ^ 2 := by
  simpa using lpNorm_pow_eq_sum two_ne_zero _

lemma l2Norm_eq_sum (f : ι → E) : ‖f‖_[2] = (∑ i, ‖f i‖₊ ^ 2) ^ (2⁻¹ : ℝ) := by
  simpa [sqrt_eq_rpow] using lpNorm_eq_sum two_ne_zero _

lemma l1Norm_eq_sum (f : ι → E) : ‖f‖_[1] = ∑ i, ‖f i‖₊ := by simp [lpNorm_eq_sum']

lemma l0Norm_eq_zero (f : ι → E) : ‖f‖_[0] = 0 := snorm_exponent_zero

lemma linftyNorm_eq_iSup (f : ι → E) : ‖f‖_[∞] = ⨆ i, ↑‖f i‖₊ := by simp

@[simp] lemma lpNorm_zero : ‖(0 : ι → E)‖_[p] = 0 := by
  obtain p | p := p; swap
  obtain rfl | hp := @eq_zero_or_pos _ _ p
  all_goals simp [linftyNorm_eq_iSup, l0Norm_eq_zero, lpNorm_eq_sum, *, ne_of_gt]

@[simp] lemma lpNorm_of_isEmpty [IsEmpty ι] (p : ℝ≥0∞) (f : ι → E) : ‖f‖_[p] = 0 := by
  simp [Subsingleton.elim f 0]

@[simp] lemma lpNorm_norm (p : ℝ≥0∞) (f : ι → E) : ‖fun i ↦ ‖f i‖‖_[p] = ‖f‖_[p] := by
  obtain p | p := p; swap
  obtain rfl | hp := @eq_zero_or_pos _ _ p
  all_goals simp [linftyNorm_eq_iSup, l0Norm_eq_zero, lpNorm_eq_sum, *, ne_of_gt]

@[simp] lemma lpNorm_neg (f : ι → E) : ‖-f‖_[p] = ‖f‖_[p] := by simp [←lpNorm_norm _ (-f)]

lemma lpNorm_sub_comm (f g : ι → E) : ‖f - g‖_[p] = ‖g - f‖_[p] := by simp [←lpNorm_neg (f - g)]

@[simp] lemma lpNorm_eq_zero (hp : p ≠ 0) : ‖f‖_[p] = 0 ↔ f = 0 := by
  obtain p | p := p
  · simp [Function.funext_iff]
  · have hp' : p ≠ 0 := by simpa [pos_iff_ne_zero] using hp
    replace hp : 0 < (p : ℝ) := by simpa [pos_iff_ne_zero] using hp
    rw [← ENNReal.rpow_eq_zero_iff_of_pos hp, ENNReal.some_eq_coe, lpNorm_rpow_eq_sum hp']
    simp [lpNorm_rpow_eq_sum, sum_eq_zero_iff_of_nonneg, rpow_nonneg, Function.funext_iff,
      ENNReal.rpow_eq_zero_iff_of_pos hp, hp']

@[simp] lemma lpNorm_pos (hp : p ≠ 0) : 0 < ‖f‖_[p] ↔ f ≠ 0 :=
  pos_iff_ne_zero.trans (lpNorm_eq_zero hp).not

lemma lpNorm_mono_right (hpq : p ≤ q) (f : ι → E) : ‖f‖_[p] ≤ ‖f‖_[q] := sorry

section one_le

lemma lpNorm_add_le (hp : 1 ≤ p) (f g : ι → E) : ‖f + g‖_[p] ≤ ‖f‖_[p] + ‖g‖_[p] :=
  snorm_add_le .of_discrete .of_discrete hp

lemma lpNorm_sum_le (hp : 1 ≤ p) {κ : Type*} (s : Finset κ) (f : κ → ι → E) :
    ‖∑ i ∈ s, f i‖_[p] ≤ ∑ i ∈ s, ‖f i‖_[p] :=
  snorm_sum_le (fun _ _ ↦ .of_discrete) hp

lemma lpNorm_sub_le (hp : 1 ≤ p) (f g : ι → E) : ‖f - g‖_[p] ≤ ‖f‖_[p] + ‖g‖_[p] :=
  snorm_sub_le .of_discrete .of_discrete hp

lemma lpNorm_le_lpNorm_add_lpNorm_sub' (hp : 1 ≤ p) (f g : ι → E) :
    ‖f‖_[p] ≤ ‖g‖_[p] + ‖f - g‖_[p] := by simpa using lpNorm_add_le hp g (f - g)

lemma lpNorm_le_lpNorm_add_lpNorm_sub (hp : 1 ≤ p) (f g : ι → E) :
    ‖f‖_[p] ≤ ‖g‖_[p] + ‖g - f‖_[p] := by
  simpa [neg_add_eq_sub] using lpNorm_add_le hp (-g) (g - f)

lemma lpNorm_le_add_lpNorm_add (hp : 1 ≤ p) (f g : ι → E) : ‖f‖_[p] ≤ ‖f + g‖_[p] + ‖g‖_[p] := by
  simpa using lpNorm_add_le hp (f + g) (-g)

lemma lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub (hp : 1 ≤ p) (f g : ι → E) :
    ‖f - h‖_[p] ≤ ‖f - g‖_[p] + ‖g - h‖_[p] := by
  simpa using lpNorm_add_le hp (f - g) (g - h)

end one_le

lemma lpNorm_smul [NormedField 𝕜] [NormedSpace 𝕜 E] (p : ℝ≥0∞) (c : 𝕜) (f : ι → E) :
    ‖c • f‖_[p] = ‖c‖₊ * ‖f‖_[p] := snorm_const_smul _ _

lemma lpNorm_nsmul [NormedSpace ℝ E] (p : ℝ≥0∞) (n : ℕ) (f : ι → E) :
    ‖n • f‖_[p] = n • ‖f‖_[p] := by simpa [natCast_smul] using lpNorm_smul p (n : ℝ) f

@[simp]
lemma lpNorm_const {p : ℝ≥0} (hp : p ≠ 0) (a : E) :
    ‖const ι a‖_[p] = Fintype.card ι ^ (p⁻¹ : ℝ) * ‖a‖₊ := by
  simp only [lpNorm_eq_sum hp, const_apply, sum_const, card_univ, nsmul_eq_mul, ENNReal.coe_mul,
    ENNReal.coe_natCast, inv_nonneg, NNReal.zero_le_coe, ENNReal.mul_rpow_of_nonneg,
    ← ENNReal.coe_rpow_of_nonneg, ENNReal.rpow_rpow_inv (NNReal.coe_ne_zero.2 hp)]

section RCLike
variable [RCLike 𝕜] {p : ℝ≥0} {f g : ι → 𝕜}

@[simp] lemma lpNorm_one (hp : p ≠ 0) : ‖(1 : ι → 𝕜)‖_[p] = Fintype.card ι ^ (p⁻¹ : ℝ) :=
  (lpNorm_const hp 1).trans $ by simp

lemma lpNorm_natCast_mul (p : ℝ≥0∞) (n : ℕ) (f : ι → 𝕜) :
    ‖(n : ι → 𝕜) * f‖_[p] = n * ‖f‖_[p] := by simpa only [nsmul_eq_mul] using lpNorm_nsmul p n f

lemma lpNorm_natCast_mul' (p : ℝ≥0∞) (n : ℕ) (f : ι → 𝕜) :
    ‖(n * f ·)‖_[p] = n * ‖f‖_[p] := lpNorm_natCast_mul p _ _

lemma lpNorm_mul_natCast (p : ℝ≥0∞) (f : ι → 𝕜) (n : ℕ) :
    ‖f * (n : ι → 𝕜)‖_[p] = ‖f‖_[p] * n := by simpa only [mul_comm] using lpNorm_natCast_mul p n f

lemma lpNorm_mul_natCast' (p : ℝ≥0∞) (f : ι → 𝕜) (n : ℕ) :
    ‖(f · * n)‖_[p] = ‖f‖_[p] * n := lpNorm_mul_natCast p _ _

lemma lpNorm_div_natCast (p : ℝ≥0∞) (f : ι → 𝕜) {n : ℕ} (hn : n ≠ 0) :
    ‖f / (n : ι → 𝕜)‖_[p] = ‖f‖_[p] / n := by
  rw [ENNReal.eq_div_iff (by positivity), mul_comm, ← lpNorm_mul_natCast] <;> simp [Pi.mul_def, hn]

lemma lpNorm_div_natCast' (p : ℝ≥0∞) (f : ι → 𝕜) {n : ℕ} (hn : n ≠ 0) :
    ‖(f · / n)‖_[p] = ‖f‖_[p] / n := lpNorm_div_natCast p _ hn

end RCLike

section Real
variable {p : ℝ≥0} {f g : ι → ℝ}

lemma lpNorm_mono (hf : 0 ≤ f) (hfg : f ≤ g) : ‖f‖_[p] ≤ ‖g‖_[p] :=
  snorm_mono_real fun i ↦ by simpa [norm_of_nonneg (hf i)] using hfg i

end Real

/-! #### Inner product -/

section CommSemiring
variable [CommSemiring 𝕜] [StarRing 𝕜] {γ : Type*} [DistribSMul γ 𝕜]

/-- Inner product giving rise to the L2 norm. -/
def l2Inner (f g : ι → 𝕜) : 𝕜 := ∑ i, conj (f i) * g i

notation "⟪" f ", " g "⟫_[" 𝕜 "]" => @l2Inner _ 𝕜 _ _ _ f g

lemma l2Inner_eq_sum (f g : ι → 𝕜) : ⟪f, g⟫_[𝕜] = ∑ i, conj (f i) * g i := rfl

@[simp] lemma conj_l2Inner (f g : ι → 𝕜) : conj ⟪f, g⟫_[𝕜] = ⟪g, f⟫_[𝕜] := by
  simp [l2Inner_eq_sum, map_sum, mul_comm]

@[simp] lemma l2Inner_zero_left (g : ι → 𝕜) : ⟪0, g⟫_[𝕜] = 0 := by simp [l2Inner_eq_sum]
@[simp] lemma l2Inner_zero_right (f : ι → 𝕜) : ⟪f, 0⟫_[𝕜] = 0 := by simp [l2Inner_eq_sum]

@[simp] lemma l2Inner_of_isEmpty [IsEmpty ι] (f g : ι → 𝕜) : ⟪f, g⟫_[𝕜] = 0 := by
  simp [Subsingleton.elim f 0]

@[simp] lemma l2Inner_const_left (a : 𝕜) (f : ι → 𝕜) : ⟪const _ a, f⟫_[𝕜] = conj a * ∑ x, f x := by
  simp only [l2Inner_eq_sum, const_apply, mul_sum]

@[simp]
lemma l2Inner_const_right (f : ι → 𝕜) (a : 𝕜) : ⟪f, const _ a⟫_[𝕜] = (∑ x, conj (f x)) * a := by
  simp only [l2Inner_eq_sum, const_apply, sum_mul]

lemma l2Inner_add_left (f₁ f₂ g : ι → 𝕜) : ⟪f₁ + f₂, g⟫_[𝕜] = ⟪f₁, g⟫_[𝕜] + ⟪f₂, g⟫_[𝕜] := by
  simp_rw [l2Inner_eq_sum, Pi.add_apply, map_add, add_mul, sum_add_distrib]

lemma l2Inner_add_right (f g₁ g₂ : ι → 𝕜) : ⟪f, g₁ + g₂⟫_[𝕜] = ⟪f, g₁⟫_[𝕜] + ⟪f, g₂⟫_[𝕜] := by
  simp_rw [l2Inner_eq_sum, Pi.add_apply, mul_add, sum_add_distrib]

lemma l2Inner_smul_left [Star γ] [StarModule γ 𝕜] [IsScalarTower γ 𝕜 𝕜] (c : γ) (f g : ι → 𝕜) :
    ⟪c • f, g⟫_[𝕜] = star c • ⟪f, g⟫_[𝕜] := by
  simp only [l2Inner_eq_sum, Pi.smul_apply, smul_mul_assoc, smul_sum, starRingEnd_apply, star_smul]

lemma l2Inner_smul_right [Star γ] [StarModule γ 𝕜] [SMulCommClass γ 𝕜 𝕜] (c : γ) (f g : ι → 𝕜) :
    ⟪f, c • g⟫_[𝕜] = c • ⟪f, g⟫_[𝕜] := by
  simp only [l2Inner_eq_sum, Pi.smul_apply, mul_smul_comm, smul_sum, starRingEnd_apply, star_smul]

lemma smul_l2Inner_left [InvolutiveStar γ] [StarModule γ 𝕜] [IsScalarTower γ 𝕜 𝕜] (c : γ)
    (f g : ι → 𝕜) : c • ⟪f, g⟫_[𝕜] = ⟪star c • f, g⟫_[𝕜] := by rw [l2Inner_smul_left, star_star]

end CommSemiring

section CommRing
variable [CommRing 𝕜] [StarRing 𝕜]

@[simp]
lemma l2Inner_neg_left (f g : ι → 𝕜) : ⟪-f, g⟫_[𝕜] = -⟪f, g⟫_[𝕜] := by simp [l2Inner_eq_sum]

@[simp]
lemma l2Inner_neg_right (f g : ι → 𝕜) : ⟪f, -g⟫_[𝕜] = -⟪f, g⟫_[𝕜] := by simp [l2Inner_eq_sum]

lemma l2Inner_sub_left (f₁ f₂ g : ι → 𝕜) : ⟪f₁ - f₂, g⟫_[𝕜] = ⟪f₁, g⟫_[𝕜] - ⟪f₂, g⟫_[𝕜] := by
  simp_rw [sub_eq_add_neg, l2Inner_add_left, l2Inner_neg_left]

lemma l2Inner_sub_right (f g₁ g₂ : ι → 𝕜) : ⟪f, g₁ - g₂⟫_[𝕜] = ⟪f, g₁⟫_[𝕜] - ⟪f, g₂⟫_[𝕜] := by
  simp_rw [sub_eq_add_neg, l2Inner_add_right, l2Inner_neg_right]

end CommRing

section OrderedCommSemiring
variable [OrderedCommSemiring 𝕜] [StarRing 𝕜] [StarOrderedRing 𝕜] {f g : ι → 𝕜}

lemma l2Inner_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[𝕜] :=
  sum_nonneg fun _ _ ↦ mul_nonneg (star_nonneg_iff.2 $ hf _) $ hg _

end OrderedCommSemiring

section LinearOrderedCommRing
variable [LinearOrderedCommRing 𝕜] [StarRing 𝕜] [StarOrderedRing 𝕜] [TrivialStar 𝕜] {f g : ι → 𝕜}

--TODO: Can we remove the `TrivialStar` assumption?
lemma abs_l2Inner_le_l2Inner_abs : |⟪f, g⟫_[𝕜]| ≤ ⟪|f|, |g|⟫_[𝕜] :=
  (abs_sum_le_sum_abs _ _).trans_eq $
    sum_congr rfl fun i _ ↦ by simp only [abs_mul, conj_trivial, Pi.abs_apply]

end LinearOrderedCommRing

section RCLike
variable {κ : Type*} [RCLike 𝕜] {f : ι → 𝕜}

lemma l2Inner_eq_inner (f g : ι → 𝕜) :
    ⟪f, g⟫_[𝕜] = inner ((WithLp.equiv 2 _).symm f) ((WithLp.equiv 2 _).symm g) := rfl

lemma inner_eq_l2Inner (f g : PiLp 2 fun _i : ι ↦ 𝕜) :
    inner f g = ⟪WithLp.equiv 2 _ f, WithLp.equiv 2 _ g⟫_[𝕜] := rfl

@[simp] lemma l2Inner_self (f : ι → 𝕜) : ⟪f, f⟫_[𝕜] = (‖f‖_[2] : 𝕜) ^ 2 := by
  simp_rw [←algebraMap.coe_pow, l2Norm_sq_eq_sum, l2Inner_eq_sum, algebraMap.coe_sum,
    RCLike.ofReal_pow, RCLike.conj_mul]

lemma l2Inner_self_of_norm_eq_one (hf : ∀ x, ‖f x‖₊ = 1) : ⟪f, f⟫_[𝕜] = Fintype.card ι := by
  simp [-l2Inner_self, l2Inner_eq_sum, RCLike.conj_mul, hf, card_univ]

lemma linearIndependent_of_ne_zero_of_l2Inner_eq_zero {v : κ → ι → 𝕜} (hz : ∀ k, v k ≠ 0)
    (ho : Pairwise fun k l ↦ ⟪v k, v l⟫_[𝕜] = 0) : LinearIndependent 𝕜 v := by
  simp_rw [l2Inner_eq_inner] at ho
  have := linearIndependent_of_ne_zero_of_inner_eq_zero ?_ ho
  exacts [this, hz]

end RCLike

section lpNorm
variable {α β : Type*} [AddCommGroup α] [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
  {p : ℝ≥0∞}

@[simp] lemma lpNorm_conj [RCLike β] (f : α → β) : ‖conj f‖_[p] = ‖f‖_[p] := by
  obtain p | p := p; swap; obtain rfl | hp := eq_or_ne p 0
  all_goals
    simp only [linftyNorm_eq_iSup, lpNorm_eq_sum, l0Norm_eq_zero, ENNReal.some_eq_coe,
      ENNReal.none_eq_top, ENNReal.coe_zero, Pi.conj_apply, RCLike.norm_conj, map_ne_zero, *]
  · simp only [lpNorm_eq_sum hp, Pi.conj_apply, RCLike.norm_conj]

end lpNorm

section RCLike
variable {α β : Type*} [Fintype α]

lemma l1Norm_mul [RCLike β] (f g : α → β) :
    ‖f * g‖_[1] = ⟪fun i ↦ ‖f i‖, fun i ↦ ‖g i‖⟫_[ℝ] := by simp [l2Inner_eq_sum, l1Norm_eq_sum]

end RCLike

/-- **Cauchy-Schwarz inequality** -/
lemma l2Inner_le_l2Norm_mul_l2Norm (f g : ι → ℝ) : ⟪f, g⟫_[ℝ] ≤ ‖f‖_[2] * ‖g‖_[2] :=
  real_inner_le_norm ((WithLp.equiv 2 _).symm f) _

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

private alias ⟨_, lpNorm_pos_of_ne_zero⟩ := lpNorm_pos

private lemma lpNorm_pos_of_pos {α : ι → Type*} [NormedAddCommGroup E]
    [Preorder E] {p : ℝ≥0∞} {f : ι → E} (hf : 0 < f) : 0 < ‖f‖_[p] :=
  lpNorm_pos_of_ne_zero hf.ne'

section OrderedCommSemiring
variable [OrderedCommSemiring 𝕜] [StarRing 𝕜] [StarOrderedRing 𝕜] {f g : ι → 𝕜}

private lemma l2Inner_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[𝕜] :=
  l2Inner_nonneg hf.le hg

private lemma l2Inner_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫_[𝕜] :=
  l2Inner_nonneg hf hg.le

private lemma l2Inner_nonneg_of_pos_of_pos (hf : 0 < f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫_[𝕜] :=
  l2Inner_nonneg hf.le hg.le

end OrderedCommSemiring

/-- The `positivity` extension which identifies expressions of the form `‖f‖_[p]`. -/
@[positivity ‖_‖_[_]] def evalLpNorm : PositivityExt where eval {u} α _z _p e := do
  if let 0 := u then -- lean4#3060 means we can't combine this with the match below
    match α, e with
    | ~q(ℝ), ~q(@lpNorm $ι $instι $α $instnorm $p $f) =>
      try
        let _pα ← synthInstanceQ (q(∀ i, PartialOrder ($α i)) : Q(Type (max u_1 u_2)))
        assumeInstancesCommute
        match ← core q(inferInstance) q(inferInstance) f with
        | .positive pf => return .positive q(lpNorm_pos_of_pos $pf)
        | .nonzero pf => return .positive q(lpNorm_pos_of_ne_zero $pf)
        | _ => return .nonnegative q(lpNorm_nonneg)
      catch _ =>
        assumeInstancesCommute
        if let some pf ← findLocalDeclWithType? q($f ≠ 0) then
          let pf : Q($f ≠ 0) := .fvar pf
          return .positive q(lpNorm_pos_of_ne_zero $pf)
        else
          return .nonnegative q(lpNorm_nonneg)
    | _ => throwError "not lpNorm"
  else
    throwError "not lpNorm"

/-- The `positivity` extension which identifies expressions of the form `⟪f, g⟫_[𝕜]`. -/
@[positivity ⟪_, _⟫_[_]] def evalL2Inner : PositivityExt where eval {u 𝕜} _ _ e := do
  match e with
  | ~q(@l2Inner $ι _ $instι $instring $inststar $f $g) =>
      let _p𝕜 ← synthInstanceQ q(OrderedCommSemiring $𝕜)
      let _p𝕜 ← synthInstanceQ q(StarOrderedRing $𝕜)
      assumeInstancesCommute
      match ← core q(inferInstance) q(inferInstance) f,
        ← core q(inferInstance) q(inferInstance) g with
      | .positive pf, .positive pg => return .nonnegative q(l2Inner_nonneg_of_pos_of_pos $pf $pg)
      | .positive pf, .nonnegative pg =>
        return .nonnegative q(l2Inner_nonneg_of_pos_of_nonneg $pf $pg)
      | .nonnegative pf, .positive pg =>
        return .nonnegative q(l2Inner_nonneg_of_nonneg_of_pos $pf $pg)
      | .nonnegative pf, .nonnegative pg => return .nonnegative q(l2Inner_nonneg $pf $pg)
      | _, _ => return .none
  | _ => throwError "not l2Inner"

section Examples
section NormedAddCommGroup
variable {α : ι → Type*} [∀ i, NormedAddCommGroup E] {w : ι → ℝ≥0} {f : ι → E}

example {p : ℝ≥0∞} : 0 ≤ ‖f‖_[p] := by positivity
example {p : ℝ≥0∞} (hf : f ≠ 0) : 0 < ‖f‖_[p] := by positivity
example {p : ℝ≥0∞} {f : ι → ℝ} (hf : 0 < f) : 0 < ‖f‖_[p] := by positivity

end NormedAddCommGroup

section Complex
variable {w : ι → ℝ≥0} {f : ι → ℂ}

example {p : ℝ≥0∞} : 0 ≤ ‖f‖_[p] := by positivity
example {p : ℝ≥0∞} (hf : f ≠ 0) : 0 < ‖f‖_[p] := by positivity
example {p : ℝ≥0∞} {f : ι → ℝ} (hf : 0 < f) : 0 < ‖f‖_[p] := by positivity

end Complex

section OrderedCommSemiring
variable [OrderedCommSemiring 𝕜] [StarRing 𝕜] [StarOrderedRing 𝕜] {f g : ι → 𝕜}

example (hf : 0 < f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫_[𝕜] := by positivity
example (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[𝕜] := by positivity
example (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫_[𝕜] := by positivity
example (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[𝕜] := by positivity

end OrderedCommSemiring
end Examples
end Mathlib.Meta.Positivity

/-! ### Hölder inequality -/

section Real
variable {α : Type*} [Fintype α] {p q : ℝ≥0} {f g : α → ℝ}

@[simp]
lemma lpNorm_abs (p : ℝ≥0∞) (f : α → ℝ) : ‖|f|‖_[p] = ‖f‖_[p] := by simpa using lpNorm_norm p f

lemma l1Norm_mul_of_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f * g‖_[1] = ⟪f, g⟫_[ℝ] := by
  convert l1Norm_mul f g using 2 <;> ext a <;> refine (norm_of_nonneg ?_).symm; exacts [hf _, hg _]

lemma lpNorm_rpow (hp : p ≠ 0) (hq : q ≠ 0) (hf : 0 ≤ f) :
    ‖f ^ (q : ℝ)‖_[p] = ‖f‖_[p * q] ^ (q : ℝ) := by
  refine rpow_left_injOn (NNReal.coe_ne_zero.2 hp) lpNorm_nonneg (by dsimp; positivity) ?_
  dsimp
  rw [←rpow_mul lpNorm_nonneg, ←mul_comm, ←ENNReal.coe_mul, ←NNReal.coe_mul,
    lpNorm_rpow_eq_sum hp, lpNorm_rpow_eq_sum (mul_ne_zero hq hp)]
  simp [abs_rpow_of_nonneg (hf _), ←rpow_mul]

lemma lpNorm_pow (hp : p ≠ 0) {q : ℕ} (hq : q ≠ 0) (f : α → ℂ) :
    ‖f ^ q‖_[p] = ‖f‖_[p * q] ^ q := by
  refine rpow_left_injOn (NNReal.coe_ne_zero.2 hp) lpNorm_nonneg (by dsimp; positivity) ?_
  dsimp
  rw [← rpow_natCast_mul lpNorm_nonneg, ← mul_comm, ← ENNReal.coe_natCast, ← ENNReal.coe_mul,
    ← NNReal.coe_natCast, ←NNReal.coe_mul, lpNorm_rpow_eq_sum hp, lpNorm_rpow_eq_sum]
  simp [← rpow_natCast_mul]
  positivity

lemma l1Norm_rpow (hq : q ≠ 0) (hf : 0 ≤ f) : ‖f ^ (q : ℝ)‖_[1] = ‖f‖_[q] ^ (q : ℝ) := by
  simpa only [ENNReal.coe_one, one_mul] using lpNorm_rpow one_ne_zero hq hf

lemma l1Norm_pow {q : ℕ} (hq : q ≠ 0) (f : α → ℂ) : ‖f ^ q‖_[1] = ‖f‖_[q] ^ q := by
  simpa only [ENNReal.coe_one, one_mul] using lpNorm_pow one_ne_zero hq f

/-- **Hölder's inequality**, binary case. -/
lemma l2Inner_le_lpNorm_mul_lpNorm (hpq : p.IsConjExponent q) (f g : α → ℝ) :
    ⟪f, g⟫_[ℝ] ≤ ‖f‖_[p] * ‖g‖_[q] := by
  have hp := hpq.ne_zero
  have hq := hpq.symm.ne_zero
  norm_cast at hp hq
  simpa [l2Inner_eq_sum, lpNorm_eq_sum, *] using inner_le_Lp_mul_Lq _ f g hpq.coe

/-- **Hölder's inequality**, binary case. -/
lemma abs_l2Inner_le_lpNorm_mul_lpNorm (hpq : p.IsConjExponent q) (f g : α → ℝ) :
    |⟪f, g⟫_[ℝ]| ≤ ‖f‖_[p] * ‖g‖_[q] :=
  abs_l2Inner_le_l2Inner_abs.trans $
    (l2Inner_le_lpNorm_mul_lpNorm hpq _ _).trans_eq $ by simp_rw [lpNorm_abs]

end Real

section Hoelder
variable {α : Type*} [Fintype α] [RCLike 𝕜] {p q : ℝ≥0} {f g : α → 𝕜}

lemma lpNorm_eq_l1Norm_rpow (hp : p ≠ 0) (f : α → 𝕜) :
    ‖f‖_[p] = ‖fun a ↦ ‖f a‖₊ ^ (p : ℝ)‖_[1] ^ (p⁻¹ : ℝ) := by
  simp [lpNorm_eq_sum hp, l1Norm_eq_sum, abs_rpow_of_nonneg]

lemma lpNorm_rpow' (hp : p ≠ 0) (hq : q ≠ 0) (f : α → 𝕜) :
    ‖f‖_[p] ^ (q : ℝ) = ‖(fun a ↦ ‖f a‖) ^ (q : ℝ)‖_[p / q] := by
  rw [←ENNReal.coe_div hq, lpNorm_rpow (div_ne_zero hp hq) hq (fun _ ↦ norm_nonneg _), lpNorm_norm,
    ← ENNReal.coe_mul, div_mul_cancel₀ _ hq]

lemma norm_l2Inner_le (f g : α → 𝕜) : ‖⟪f, g⟫_[𝕜]‖₊ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫_[ℝ] :=
  (norm_sum_le _ _).trans $ by simp [l2Inner]

/-- **Hölder's inequality**, binary case. -/
lemma norm_l2Inner_le_lpNorm_mul_lpNorm (hpq : p.IsConjExponent q) (f g : α → 𝕜) :
    ‖⟪f, g⟫_[𝕜]‖₊ ≤ ‖f‖_[p] * ‖g‖_[q] :=
  calc
    _ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫_[ℝ] := norm_l2Inner_le _ _
    _ ≤ ‖fun a ↦ ‖f a‖‖_[p] * ‖fun a ↦ ‖g a‖‖_[q] := l2Inner_le_lpNorm_mul_lpNorm hpq _ _
    _ = ‖f‖_[p] * ‖g‖_[q] := by simp_rw [lpNorm_norm]

/-- **Hölder's inequality**, binary case. -/
lemma lpNorm_mul_le (hp : p ≠ 0) (hq : q ≠ 0) (r : ℝ≥0) (hpqr : p⁻¹ + q⁻¹ = r⁻¹) (f g : α → 𝕜) :
    ‖f * g‖_[r] ≤ ‖f‖_[p] * ‖g‖_[q] := by
  have hr : r ≠ 0 := by
    rintro rfl
    simp [hp] at hpqr
  have : (‖(f * g) ·‖₊ ^ (r : ℝ)) = (‖f ·‖₊ ^ (r : ℝ)) * (‖g ·‖₊ ^ (r : ℝ)) := by
    ext; simp [mul_rpow, abs_mul]
  rw [lpNorm_eq_l1Norm_rpow, rpow_inv_le_iff_of_pos, this, l1Norm_mul_of_nonneg,
    mul_rpow lpNorm_nonneg lpNorm_nonneg, lpNorm_rpow', lpNorm_rpow', ←ENNReal.coe_div, ←
    ENNReal.coe_div]
  refine l2Inner_le_lpNorm_mul_lpNorm ⟨?_, ?_⟩ _ _
  · norm_cast
    rw [div_eq_mul_inv, ←hpqr, mul_add, mul_inv_cancel hp]
    exact lt_add_of_pos_right _ (by positivity)
  · norm_cast
    simp [div_eq_mul_inv, hpqr, ←mul_add, hr]
  any_goals intro a; dsimp
  all_goals positivity

/-- **Hölder's inequality**, binary case. -/
lemma l1Norm_mul_le (hpq : p.IsConjExponent q) (f g : α → 𝕜) :
    ‖f * g‖_[1] ≤ ‖f‖_[p] * ‖g‖_[q] :=
  lpNorm_mul_le (mod_cast hpq.ne_zero) (mod_cast hpq.symm.ne_zero) _
    (by simpa using hpq.inv_add_inv_conj) _ _

/-- **Hölder's inequality**, finitary case. -/
lemma lpNorm_prod_le {s : Finset ι} (hs : s.Nonempty) {p : ι → ℝ≥0} (hp : ∀ i, p i ≠ 0) (q : ℝ≥0)
    (hpq : ∑ i in s, (p i)⁻¹ = q⁻¹) (f : ι → α → 𝕜) :
    ‖∏ i in s, f i‖_[q] ≤ ∏ i in s, ‖f i‖_[p i] := by
  induction' s using Finset.cons_induction with i s hi ih generalizing q
  · cases not_nonempty_empty hs
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp only [sum_cons, sum_empty, add_zero, inv_inj] at hpq
    simp [←hpq]
  simp_rw [prod_cons]
  rw [sum_cons, ←inv_inv (∑ _ ∈ _, _ : ℝ≥0)] at hpq
  refine
    (lpNorm_mul_le (hp _) (inv_ne_zero (sum_pos (fun _ _ ↦ ?_) hs).ne') _ hpq _ _).trans
      (mul_le_mul_of_nonneg_left (ih hs _ (inv_inv _).symm) lpNorm_nonneg)
  exact pos_iff_ne_zero.2 (inv_ne_zero $ hp _)

end Hoelder

section
variable {α : Type*} [Fintype α]

@[simp]
lemma RCLike.lpNorm_coe_comp {𝕜 : Type*} [RCLike 𝕜] (p) (f : α → ℝ) :
    ‖((↑) : ℝ → 𝕜) ∘ f‖_[p] = ‖f‖_[p] := by
  simp only [←lpNorm_norm _ (((↑) : ℝ → 𝕜) ∘ f), ←lpNorm_norm _ f, Function.comp_apply,
    RCLike.norm_ofReal, Real.norm_eq_abs]

@[simp] lemma Complex.lpNorm_coe_comp (p) (f : α → ℝ) : ‖((↑) : ℝ → ℂ) ∘ f‖_[p] = ‖f‖_[p] :=
  RCLike.lpNorm_coe_comp _ _

end
