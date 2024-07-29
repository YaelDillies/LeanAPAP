import Mathlib.Data.Finset.Density
import LeanAPAP.Prereqs.LpNorm.Discrete.Basic

/-!
# Normalised Lp norms
-/

open Finset hiding card
open Function Real
open Fintype (card)
open scoped BigOperators ComplexConjugate ENNReal NNReal

variable {ι 𝕜 : Type*} [Fintype ι]

/-! ### Lp norm -/

section NormedAddCommGroup
variable {α : ι → Type*} [∀ i, NormedAddCommGroup (α i)] {p q : ℝ≥0∞} {f g h : ∀ i, α i}

/-- The Lp norm of a function with the compact normalisation. -/
noncomputable def nlpNorm (p : ℝ≥0∞) (f : ∀ i, α i) : ℝ := ‖f‖_[p] / (card ι : ℝ) ^ p.toReal⁻¹

notation "‖" f "‖ₙ_[" p "]" => nlpNorm p f

lemma nlpNorm_eq_expect' (hp : p.toReal ≠ 0) (f : ∀ i, α i) :
    ‖f‖ₙ_[p] = (𝔼 i, ‖f i‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  rw [nlpNorm, lpNorm_eq_sum', ← div_rpow, Fintype.expect_eq_sum_div_card (α := ℝ)] <;> positivity

lemma nlpNorm_eq_expect'' {p : ℝ} (hp : 0 < p) (f : ∀ i, α i) :
    ‖f‖ₙ_[p.toNNReal] = (𝔼 i, ‖f i‖ ^ p) ^ p⁻¹ := by
  rw [nlpNorm_eq_expect'] <;> simp [hp.ne', hp.le]

lemma nlpNorm_eq_expect {p : ℝ≥0} (hp : p ≠ 0) (f : ∀ i, α i) :
    ‖f‖ₙ_[p] = (𝔼 i, ‖f i‖ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) := nlpNorm_eq_expect' (by simpa using hp) _

lemma nlpNorm_rpow_eq_expect {p : ℝ≥0} (hp : p ≠ 0) (f : ∀ i, α i) :
    ‖f‖ₙ_[p] ^ (p : ℝ) = 𝔼 i, ‖f i‖ ^ (p : ℝ) := by
  rw [nlpNorm_eq_expect hp, rpow_inv_rpow] <;> positivity

lemma nlpNorm_pow_eq_expect {p : ℕ} (hp : p ≠ 0) (f : ∀ i, α i) :
    ‖f‖ₙ_[p] ^ p = 𝔼 i, ‖f i‖ ^ p := by
  simpa using nlpNorm_rpow_eq_expect (Nat.cast_ne_zero.2 hp) f

lemma nl2Norm_sq_eq_expect (f : ∀ i, α i) : ‖f‖ₙ_[2] ^ 2 = 𝔼 i, ‖f i‖ ^ 2 := by
  simpa using nlpNorm_pow_eq_expect two_ne_zero _

lemma nl2Norm_eq_expect (f : ∀ i, α i) : ‖f‖ₙ_[2] = sqrt (𝔼 i, ‖f i‖ ^ 2) := by
  simpa [sqrt_eq_rpow] using nlpNorm_eq_expect two_ne_zero _

lemma nl1Norm_eq_expect (f : ∀ i, α i) : ‖f‖ₙ_[1] = 𝔼 i, ‖f i‖ := by simp [nlpNorm_eq_expect']

lemma nl0Norm_eq_zero (f : ∀ i, α i) : ‖f‖ₙ_[0] = {i | f i ≠ 0}.toFinite.toFinset.card := by
  simp [l0Norm_eq_zero, nlpNorm]

lemma nlinftyNorm_eq_iSup (f : ∀ i, α i) : ‖f‖ₙ_[∞] = ⨆ i, ‖f i‖ := by
  simp [nlpNorm, linftyNorm_eq_iSup]

@[simp] lemma nlpNorm_zero : ‖(0 : ∀ i, α i)‖ₙ_[p] = 0 := by simp [nlpNorm]

@[simp] lemma nlpNorm_of_isEmpty [IsEmpty ι] (p : ℝ≥0∞) (f : ∀ i, α i) : ‖f‖ₙ_[p] = 0 := by
  simp [nlpNorm]

@[simp] lemma nlpNorm_norm (p : ℝ≥0∞) (f : ∀ i, α i) : ‖fun i ↦ ‖f i‖‖ₙ_[p] = ‖f‖ₙ_[p] := by
  simp [nlpNorm]

@[simp] lemma nlpNorm_neg (f : ∀ i, α i) : ‖-f‖ₙ_[p] = ‖f‖ₙ_[p] := by simp [←nlpNorm_norm _ (-f)]

lemma nlpNorm_sub_comm (f g : ∀ i, α i) : ‖f - g‖ₙ_[p] = ‖g - f‖ₙ_[p] := by
  simp [←nlpNorm_neg (f - g)]

@[simp] lemma nlpNorm_nonneg : 0 ≤ ‖f‖ₙ_[p] := by unfold nlpNorm; positivity

@[simp] lemma nlpNorm_eq_zero [Nonempty ι] : ‖f‖ₙ_[p] = 0 ↔ f = 0 := by
  obtain p | p := p
  · simp [nlinftyNorm_eq_iSup, ENNReal.none_eq_top, ←sup'_univ_eq_ciSup, le_antisymm_iff,
      Function.funext_iff]
  obtain rfl | hp := eq_or_ne p 0
  · simp [nl0Norm_eq_zero, eq_empty_iff_forall_not_mem, Function.funext_iff]
  · rw [←rpow_eq_zero nlpNorm_nonneg (NNReal.coe_ne_zero.2 hp)]
    simp [nlpNorm_rpow_eq_expect hp, Fintype.expect_eq_zero_iff_of_nonneg, rpow_nonneg,
      Function.funext_iff, rpow_eq_zero _ (NNReal.coe_ne_zero.2 hp), Pi.le_def]

@[simp] lemma nlpNorm_pos [Nonempty ι] : 0 < ‖f‖ₙ_[p] ↔ f ≠ 0 :=
  nlpNorm_nonneg.gt_iff_ne.trans nlpNorm_eq_zero.not

lemma nlpNorm_mono_right (hpq : p ≤ q) (f : ∀ i, α i) : ‖f‖ₙ_[p] ≤ ‖f‖ₙ_[q] := sorry

section one_le

lemma nlpNorm_add_le (hp : 1 ≤ p) (f g : ∀ i, α i) : ‖f + g‖ₙ_[p] ≤ ‖f‖ₙ_[p] + ‖g‖ₙ_[p] := by
  simp only [nlpNorm, ← add_div]
  exact div_le_div_of_nonneg_right (lpNorm_add_le hp _ _) (by positivity)

lemma nlpNorm_sub_le (hp : 1 ≤ p) (f g : ∀ i, α i) : ‖f - g‖ₙ_[p] ≤ ‖f‖ₙ_[p] + ‖g‖ₙ_[p] := by
  simp only [nlpNorm, ← add_div]
  exact div_le_div_of_nonneg_right (lpNorm_sub_le hp _ _) (by positivity)

lemma nlpNorm_le_nlpNorm_add_nlpNorm_sub' (hp : 1 ≤ p) (f g : ∀ i, α i) :
    ‖f‖ₙ_[p] ≤ ‖g‖ₙ_[p] + ‖f - g‖ₙ_[p] := by
  simp only [nlpNorm, ← add_div]
  exact div_le_div_of_nonneg_right (lpNorm_le_lpNorm_add_lpNorm_sub' hp _ _) (by positivity)

lemma nlpNorm_le_nlpNorm_add_nlpNorm_sub (hp : 1 ≤ p) (f g : ∀ i, α i) :
    ‖f‖ₙ_[p] ≤ ‖g‖ₙ_[p] + ‖g - f‖ₙ_[p] := by
  simp only [nlpNorm, ← add_div]
  exact div_le_div_of_nonneg_right (lpNorm_le_lpNorm_add_lpNorm_sub hp _ _) (by positivity)

lemma nlpNorm_le_add_nlpNorm_add (hp : 1 ≤ p) (f g : ∀ i, α i) :
    ‖f‖ₙ_[p] ≤ ‖f + g‖ₙ_[p] + ‖g‖ₙ_[p] := by
  simp only [nlpNorm, ← add_div]
  exact div_le_div_of_nonneg_right (lpNorm_le_add_lpNorm_add hp _ _) (by positivity)

lemma nlpNorm_sub_le_nlpNorm_sub_add_nlpNorm_sub (hp : 1 ≤ p) (f g : ∀ i, α i) :
    ‖f - h‖ₙ_[p] ≤ ‖f - g‖ₙ_[p] + ‖g - h‖ₙ_[p] := by
  simp only [nlpNorm, ← add_div]
  exact div_le_div_of_nonneg_right (lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub hp _ _) (by positivity)

variable [NormedField 𝕜] [∀ i, NormedSpace 𝕜 (α i)]

-- TODO: `p ≠ 0` is enough
lemma nlpNorm_smul (hp : 1 ≤ p) (c : 𝕜) (f : ∀ i, α i) : ‖c • f‖ₙ_[p] = ‖c‖ * ‖f‖ₙ_[p] := by
  simp only [nlpNorm, mul_div_assoc, lpNorm_smul hp]

variable [∀ i, NormedSpace ℝ (α i)]

lemma nlpNorm_nsmul (hp : 1 ≤ p) (n : ℕ) (f : ∀ i, α i) : ‖n • f‖ₙ_[p] = n • ‖f‖ₙ_[p] := by
  simp only [nlpNorm, nsmul_eq_mul, mul_div_assoc, lpNorm_nsmul hp]

end one_le
end NormedAddCommGroup

section NormedAddCommGroup
variable {α : Type*} [NormedAddCommGroup α] {p : ℝ≥0∞}

@[simp]
lemma nlpNorm_const [Nonempty ι] (hp : p ≠ 0) (a : α) : ‖const ι a‖ₙ_[p] = ‖a‖ := by
  obtain _ | p := p
  · simp [nlinftyNorm_eq_iSup]
  have : (card ι : ℝ) ^ (p : ℝ)⁻¹ ≠ 0 := by positivity
  simp [nlpNorm, ENNReal.coe_ne_coe.1 hp, mul_div_cancel_left₀ _ this]

end NormedAddCommGroup

section RCLike
variable [RCLike 𝕜] {p : ℝ≥0∞} {f g : ι → 𝕜}

@[simp] lemma nlpNorm_one [Nonempty ι] (hp : p ≠ 0) : ‖(1 : ι → 𝕜)‖ₙ_[p] = 1 :=
  (nlpNorm_const hp 1).trans $ by simp

lemma nlpNorm_natCast_mul (hp : 1 ≤ p) (n : ℕ) (f : ι → 𝕜) :
    ‖(n : ι → 𝕜) * f‖ₙ_[p] = n * ‖f‖ₙ_[p] := by simpa only [nsmul_eq_mul] using nlpNorm_nsmul hp n f

lemma nlpNorm_natCast_mul' (hp : 1 ≤ p) (n : ℕ) (f : ι → 𝕜) :
    ‖(n * f ·)‖ₙ_[p] = n * ‖f‖ₙ_[p] := nlpNorm_natCast_mul hp _ _

lemma nlpNorm_mul_natCast (hp : 1 ≤ p) (f : ι → 𝕜) (n : ℕ) :
    ‖f * (n : ι → 𝕜)‖ₙ_[p] = ‖f‖ₙ_[p] * n := by
  simpa only [mul_comm] using nlpNorm_natCast_mul hp n f

lemma nlpNorm_mul_natCast' (hp : 1 ≤ p) (f : ι → 𝕜) (n : ℕ) :
    ‖(f · * n)‖ₙ_[p] = ‖f‖ₙ_[p] * n := nlpNorm_mul_natCast hp _ _

lemma nlpNorm_div_natCast' (hp : 1 ≤ p) (f : ι → 𝕜) (n : ℕ) :
    ‖(f · / n)‖ₙ_[p] = ‖f‖ₙ_[p] / n := by simp [nlpNorm, lpNorm_div_natCast' hp, div_right_comm]

lemma nlpNorm_div_natCast (hp : 1 ≤ p) (f : ι → 𝕜) (n : ℕ) :
    ‖f / (n : ι → 𝕜)‖ₙ_[p] = ‖f‖ₙ_[p] / n := nlpNorm_div_natCast' hp _ _

end RCLike

section Real
variable {p : ℝ≥0} {f g : ι → ℝ}

lemma nlpNorm_mono (hf : 0 ≤ f) (hfg : f ≤ g) : ‖f‖ₙ_[p] ≤ ‖g‖ₙ_[p] :=
  div_le_div_of_nonneg_right (lpNorm_mono hf hfg) $ by positivity

end Real

/-! #### Inner product -/

section Semifield
variable [Semifield 𝕜] [CharZero 𝕜] [StarRing 𝕜] {γ : Type*} [DistribSMul γ 𝕜]

/-- Inner product giving rise to the L2 norm with the compact normalisation. -/
def nl2Inner (f g : ι → 𝕜) : 𝕜 := 𝔼 i, conj (f i) * g i

notation "⟪" f ", " g "⟫ₙ_[" 𝕜 "]" => @nl2Inner _ 𝕜 _ _ _ _ f g

lemma nl2Inner_eq_expect (f g : ι → 𝕜) : ⟪f, g⟫ₙ_[𝕜] = 𝔼 i, conj (f i) * g i := rfl
lemma nl2Inner_eq_l2Inner_div_card (f g : ι → 𝕜) : ⟪f, g⟫ₙ_[𝕜] = ⟪f, g⟫_[𝕜] / card ι :=
  Fintype.expect_eq_sum_div_card _

@[simp] lemma conj_nl2Inner (f g : ι → 𝕜) : conj ⟪f, g⟫ₙ_[𝕜] = ⟪g, f⟫ₙ_[𝕜] := by
  simp [nl2Inner_eq_expect, map_expect, mul_comm]

@[simp] lemma nl2Inner_zero_left (g : ι → 𝕜) : ⟪0, g⟫ₙ_[𝕜] = 0 := by simp [nl2Inner]
@[simp] lemma nl2Inner_zero_right (f : ι → 𝕜) : ⟪f, 0⟫ₙ_[𝕜] = 0 := by simp [nl2Inner]

@[simp] lemma nl2Inner_of_isEmpty [IsEmpty ι] (f g : ι → 𝕜) : ⟪f, g⟫ₙ_[𝕜] = 0 := by
  simp [nl2Inner_eq_l2Inner_div_card]

@[simp] lemma nl2Inner_const_left (a : 𝕜) (f : ι → 𝕜) :
    ⟪const _ a, f⟫ₙ_[𝕜] = conj a * 𝔼 x, f x := by
  simp only [nl2Inner, const_apply, mul_expect]

@[simp]
lemma nl2Inner_const_right (f : ι → 𝕜) (a : 𝕜) : ⟪f, const _ a⟫ₙ_[𝕜] = (𝔼 x, conj (f x)) * a := by
  simp only [nl2Inner, const_apply, expect_mul]

lemma nl2Inner_add_left (f₁ f₂ g : ι → 𝕜) : ⟪f₁ + f₂, g⟫ₙ_[𝕜] = ⟪f₁, g⟫ₙ_[𝕜] + ⟪f₂, g⟫ₙ_[𝕜] := by
  simp_rw [nl2Inner, Pi.add_apply, map_add, add_mul, expect_add_distrib]

lemma nl2Inner_add_right (f g₁ g₂ : ι → 𝕜) : ⟪f, g₁ + g₂⟫ₙ_[𝕜] = ⟪f, g₁⟫ₙ_[𝕜] + ⟪f, g₂⟫ₙ_[𝕜] := by
  simp_rw [nl2Inner, Pi.add_apply, mul_add, expect_add_distrib]

lemma nl2Inner_smul_left [Star γ] [StarModule γ 𝕜] [SMulCommClass γ ℚ≥0 𝕜]
    [IsScalarTower γ 𝕜 𝕜] (c : γ) (f g : ι → 𝕜) :
    ⟪c • f, g⟫ₙ_[𝕜] = star c • ⟪f, g⟫ₙ_[𝕜] := by
  simp only [nl2Inner, Pi.smul_apply, smul_mul_assoc, smul_expect, starRingEnd_apply,
    star_smul]

lemma nl2Inner_smul_right [Star γ] [StarModule γ 𝕜] [SMulCommClass γ ℚ≥0 𝕜] [IsScalarTower γ 𝕜 𝕜]
    [SMulCommClass γ 𝕜 𝕜] (c : γ) (f g : ι → 𝕜) : ⟪f, c • g⟫ₙ_[𝕜] = c • ⟪f, g⟫ₙ_[𝕜] := by
  simp only [nl2Inner, Pi.smul_apply, mul_smul_comm, smul_expect, starRingEnd_apply,
    star_smul]

lemma smul_nl2Inner_left [InvolutiveStar γ] [StarModule γ 𝕜] [SMulCommClass γ ℚ≥0 𝕜]
    [IsScalarTower γ 𝕜 𝕜] (c : γ) (f g : ι → 𝕜) : c • ⟪f, g⟫ₙ_[𝕜] = ⟪star c • f, g⟫ₙ_[𝕜] := by
  rw [nl2Inner_smul_left, star_star]

end Semifield

section Field
variable [Field 𝕜] [CharZero 𝕜] [StarRing 𝕜]

@[simp] lemma nl2Inner_neg_left (f g : ι → 𝕜) : ⟪-f, g⟫ₙ_[𝕜] = -⟪f, g⟫ₙ_[𝕜] := by simp [nl2Inner]
@[simp] lemma nl2Inner_neg_right (f g : ι → 𝕜) : ⟪f, -g⟫ₙ_[𝕜] = -⟪f, g⟫ₙ_[𝕜] := by simp [nl2Inner]

lemma nl2Inner_sub_left (f₁ f₂ g : ι → 𝕜) : ⟪f₁ - f₂, g⟫ₙ_[𝕜] = ⟪f₁, g⟫ₙ_[𝕜] - ⟪f₂, g⟫ₙ_[𝕜] := by
  simp_rw [sub_eq_add_neg, nl2Inner_add_left, nl2Inner_neg_left]

lemma nl2Inner_sub_right (f g₁ g₂ : ι → 𝕜) : ⟪f, g₁ - g₂⟫ₙ_[𝕜] = ⟪f, g₁⟫ₙ_[𝕜] - ⟪f, g₂⟫ₙ_[𝕜] := by
  simp_rw [sub_eq_add_neg, nl2Inner_add_right, nl2Inner_neg_right]

end Field

section LinearOrderedSemifield
variable [LinearOrderedSemifield 𝕜] [PosSMulMono ℚ≥0 𝕜] [CharZero 𝕜] [StarRing 𝕜]
  [StarOrderedRing 𝕜] {f g : ι → 𝕜}

lemma nl2Inner_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫ₙ_[𝕜] :=
  expect_nonneg fun _ _ ↦ mul_nonneg (star_nonneg_iff.2 $ hf _) $ hg _

end LinearOrderedSemifield

section LinearOrderedField
variable [LinearOrderedField 𝕜] [StarRing 𝕜] [StarOrderedRing 𝕜] [TrivialStar 𝕜] {f g : ι → 𝕜}

--TODO: Can we remove the `TrivialStar` assumption?
lemma abs_nl2Inner_le_nl2Inner_abs : |⟪f, g⟫ₙ_[𝕜]| ≤ ⟪|f|, |g|⟫ₙ_[𝕜] :=
  (abs_expect_le_expect_abs _ _).trans_eq $
    expect_congr rfl fun i _ ↦ by simp only [abs_mul, conj_trivial, Pi.abs_apply]

end LinearOrderedField

section RCLike
variable {κ : Type*} [RCLike 𝕜] {f : ι → 𝕜}

@[simp] lemma nl2Inner_self (f : ι → 𝕜) : ⟪f, f⟫ₙ_[𝕜] = (‖f‖ₙ_[2] : 𝕜) ^ 2 := by
  simp_rw [←algebraMap.coe_pow, nl2Norm_sq_eq_expect, nl2Inner,
    algebraMap.coe_expect _ (α := ℝ) (β := 𝕜), RCLike.ofReal_pow, RCLike.conj_mul]

lemma nl2Inner_self_of_norm_eq_one [Nonempty ι] (hf : ∀ x, ‖f x‖ = 1) : ⟪f, f⟫ₙ_[𝕜] = 1 := by
  simp [-nl2Inner_self, nl2Inner, RCLike.conj_mul, hf]

lemma linearIndependent_of_ne_zero_of_nl2Inner_eq_zero {v : κ → ι → 𝕜} (hz : ∀ k, v k ≠ 0)
    (ho : Pairwise fun k l ↦ ⟪v k, v l⟫ₙ_[𝕜] = 0) : LinearIndependent 𝕜 v := by
  cases isEmpty_or_nonempty ι
  · have : IsEmpty κ := ⟨fun k ↦ hz k $ Subsingleton.elim _ _⟩
    exact linearIndependent_empty_type
  · exact linearIndependent_of_ne_zero_of_l2Inner_eq_zero hz $ by
      simpa [nl2Inner_eq_l2Inner_div_card] using ho

end RCLike

section nlpNorm
variable {α β : Type*} [AddCommGroup α] [Fintype α] {p : ℝ≥0∞}

@[simp]
lemma nlpNorm_translate [NormedAddCommGroup β] (a : α) (f : α → β) : ‖τ a f‖ₙ_[p] = ‖f‖ₙ_[p] := by
  simp [nlpNorm]

@[simp] lemma nlpNorm_conj [RCLike β] (f : α → β) : ‖conj f‖ₙ_[p] = ‖f‖ₙ_[p] := by simp [nlpNorm]

@[simp] lemma nlpNorm_conjneg [RCLike β] (f : α → β) : ‖conjneg f‖ₙ_[p] = ‖f‖ₙ_[p] := by
  simp [nlpNorm]

end nlpNorm

section RCLike
variable {α β : Type*} [Fintype α]

lemma nl1Norm_mul [RCLike β] (f g : α → β) :
    ‖f * g‖ₙ_[1] = ⟪fun i ↦ ‖f i‖, fun i ↦ ‖g i‖⟫ₙ_[ℝ] := by simp [nl2Inner, nl1Norm_eq_expect]

end RCLike

/-- **Cauchy-Schwarz inequality** -/
lemma nl2Inner_le_l2Norm_mul_l2Norm (f g : ι → ℝ) : ⟪f, g⟫ₙ_[ℝ] ≤ ‖f‖ₙ_[2] * ‖g‖ₙ_[2] := by
  simp only [nlpNorm, div_mul_div_comm, ← sq, ENNReal.toReal_ofNat, ← one_div, ← sqrt_eq_rpow]
  rw [sq_sqrt, nl2Inner_eq_l2Inner_div_card (𝕜 := ℝ)]
  refine div_le_div_of_nonneg_right (l2Inner_le_l2Norm_mul_l2Norm _ _) ?_
  all_goals positivity

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

private alias ⟨_, nlpNorm_pos_of_ne_zero⟩ := nlpNorm_pos

private lemma nlpNorm_pos_of_pos {α : ι → Type*} [Nonempty ι] [∀ i, NormedAddCommGroup (α i)]
    [∀ i, Preorder (α i)] {p : ℝ≥0∞} {f : ∀ i, α i} (hf : 0 < f) : 0 < ‖f‖ₙ_[p] :=
  nlpNorm_pos_of_ne_zero hf.ne'

section LinearOrderedSemifield
variable [LinearOrderedSemifield 𝕜] [Module ℚ≥0 𝕜] [StarRing 𝕜] [StarOrderedRing 𝕜] {f g : ι → 𝕜}

private lemma nl2Inner_nonneg_of_nonneg_of_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫ₙ_[𝕜] :=
  sorry

private lemma nl2Inner_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫ₙ_[𝕜] :=
  nl2Inner_nonneg_of_nonneg_of_nonneg hf.le hg

private lemma nl2Inner_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫ₙ_[𝕜] :=
  nl2Inner_nonneg_of_nonneg_of_nonneg hf hg.le

private lemma nl2Inner_nonneg_of_pos_of_pos (hf : 0 < f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫ₙ_[𝕜] :=
  nl2Inner_nonneg_of_nonneg_of_nonneg hf.le hg.le

end LinearOrderedSemifield

/-- The `positivity` extension which identifies expressions of the form `‖f‖ₙ_[p]`. -/
@[positivity ‖_‖ₙ_[_]] def evalNLpNorm : PositivityExt where eval {u} α _z _p e := do
  if let 0 := u then -- lean4#3060 means we can't combine this with the match below
    match α, e with
    | ~q(ℝ), ~q(@nlpNorm $ι $instι $α $instnorm $p $f) =>
      try
        let _pα ← synthInstanceQ (q(∀ i, PartialOrder ($α i)) : Q(Type (max u_1 u_2)))
        let _instιno ← synthInstanceQ (q(Nonempty $ι) : Q(Prop))
        assumeInstancesCommute
        match ← core (q(inferInstance) : Q(Zero (∀ i, $α i))) q(inferInstance) f with
        | .positive pf => return .positive q(nlpNorm_pos_of_pos $pf)
        | .nonzero pf => return .positive q(nlpNorm_pos_of_ne_zero $pf)
        | _ => return .nonnegative q(nlpNorm_nonneg)
      catch _ =>
        assumeInstancesCommute
        if let some pf ← findLocalDeclWithType? q($f ≠ 0) then
          let pf : Q($f ≠ 0) := .fvar pf
          let _instιno ← synthInstanceQ q(Nonempty $ι)
          return .positive q(nlpNorm_pos_of_ne_zero $pf)
        else
          return .nonnegative q(nlpNorm_nonneg)
    | _ => throwError "not nlpNorm"
  else
    throwError "not nlpNorm"

/-- The `positivity` extension which identifies expressions of the form `⟪f, g⟫_[𝕜]`. -/
@[positivity ⟪_, _⟫ₙ_[_]] def evalNL2Inner : PositivityExt where eval {u 𝕜} _ _ e := do
  match e with
  | ~q(@nl2Inner $ι _ $instι $instfield $instmod $inststar $f $g) =>
      let _p𝕜 ← synthInstanceQ q(LinearOrderedSemifield $𝕜)
      let _p𝕜 ← synthInstanceQ q(StarRing $𝕜)
      let _p𝕜 ← synthInstanceQ q(StarOrderedRing $𝕜)
      assumeInstancesCommute
      match ← core q(inferInstance) q(inferInstance) f,
        ← core q(inferInstance) q(inferInstance) g with
      | .positive pf, .positive pg => return .nonnegative q(nl2Inner_nonneg_of_pos_of_pos $pf $pg)
      | .positive pf, .nonnegative pg =>
        return .nonnegative q(nl2Inner_nonneg_of_pos_of_nonneg $pf $pg)
      | .nonnegative pf, .positive pg =>
        return .nonnegative q(nl2Inner_nonneg_of_nonneg_of_pos $pf $pg)
      | .nonnegative pf, .nonnegative pg =>
        return .nonnegative q(nl2Inner_nonneg_of_nonneg_of_nonneg $pf $pg)
      | _, _ => return .none
  | _ => throwError "not nl2Inner"

section Examples
section NormedAddCommGroup
variable {α : ι → Type*} [∀ i, NormedAddCommGroup (α i)] {w : ι → ℝ≥0} {f : ∀ i, α i}

example {p : ℝ≥0∞} : 0 ≤ ‖f‖ₙ_[p] := by positivity
example {p : ℝ≥0∞} [Nonempty ι] (hf : f ≠ 0) : 0 < ‖f‖ₙ_[p] := by positivity
example {p : ℝ≥0∞} [Nonempty ι] {f : ι → ℝ} (hf : 0 < f) : 0 < ‖f‖ₙ_[p] := by positivity

end NormedAddCommGroup

section Complex
variable {w : ι → ℝ≥0} {f : ι → ℂ}

example {p : ℝ≥0∞} : 0 ≤ ‖f‖ₙ_[p] := by positivity
example {p : ℝ≥0∞} [Nonempty ι] (hf : f ≠ 0) : 0 < ‖f‖ₙ_[p] := by positivity
example {p : ℝ≥0∞} [Nonempty ι] {f : ι → ℝ} (hf : 0 < f) : 0 < ‖f‖ₙ_[p] := by positivity

end Complex

section LinearOrderedSemifield
variable [LinearOrderedSemifield 𝕜] [StarRing 𝕜] [StarOrderedRing 𝕜] {f g : ι → 𝕜}

example (hf : 0 < f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫ₙ_[𝕜] := by positivity
example (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫ₙ_[𝕜] := by positivity
example (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫ₙ_[𝕜] := by positivity
example (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫ₙ_[𝕜] := by positivity

end LinearOrderedSemifield
end Examples
end Mathlib.Meta.Positivity

/-! ### Hölder inequality -/

section nlpNorm
variable {α : Type*} [Fintype α] {p q : ℝ≥0} {f g : α → ℝ}

@[simp]
lemma nlpNorm_abs (p : ℝ≥0∞) (f : α → ℝ) : ‖|f|‖ₙ_[p] = ‖f‖ₙ_[p] := by simpa using nlpNorm_norm p f

lemma nl1Norm_mul_of_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f * g‖ₙ_[1] = ⟪f, g⟫ₙ_[ℝ] := by
  convert nl1Norm_mul f g using 2 <;> ext a <;> refine (norm_of_nonneg ?_).symm; exacts [hf _, hg _]

lemma nlpNorm_rpow (hp : p ≠ 0) (hq : q ≠ 0) (hf : 0 ≤ f) :
    ‖f ^ (q : ℝ)‖ₙ_[p] = ‖f‖ₙ_[p * q] ^ (q : ℝ) := by
  refine rpow_left_injOn (NNReal.coe_ne_zero.2 hp) nlpNorm_nonneg (by dsimp; positivity) ?_
  dsimp
  rw [←rpow_mul nlpNorm_nonneg, ←mul_comm, ←ENNReal.coe_mul, ←NNReal.coe_mul,
    nlpNorm_rpow_eq_expect hp, nlpNorm_rpow_eq_expect (mul_ne_zero hq hp)]
  simp [abs_rpow_of_nonneg (hf _), ←rpow_mul]

lemma nl1Norm_rpow (hq : q ≠ 0) (hf : 0 ≤ f) : ‖f ^ (q : ℝ)‖ₙ_[1] = ‖f‖ₙ_[q] ^ (q : ℝ) := by
  simpa only [ENNReal.coe_one, one_mul] using nlpNorm_rpow one_ne_zero hq hf

lemma nlpNorm_eq_l1Norm_rpow (hp : p ≠ 0) (f : α → ℝ) :
    ‖f‖ₙ_[p] = ‖|f| ^ (p : ℝ)‖ₙ_[1] ^ (p⁻¹ : ℝ) := by
  simp [nlpNorm_eq_expect hp, nl1Norm_eq_expect, abs_rpow_of_nonneg]

lemma nlpNorm_rpow' (hp : p ≠ 0) (hq : q ≠ 0) (f : α → ℝ) :
    ‖f‖ₙ_[p] ^ (q : ℝ) = ‖|f| ^ (q : ℝ)‖ₙ_[p / q] := by
  rw [←ENNReal.coe_div hq, nlpNorm_rpow (div_ne_zero hp hq) hq (abs_nonneg f), nlpNorm_abs,
    ← ENNReal.coe_mul, div_mul_cancel₀ _ hq]

--TODO: Generalise the following four to include `f g : α → ℂ`
/-- **Hölder's inequality**, binary case. -/
lemma nl2Inner_le_nlpNorm_mul_nlpNorm (hpq : p.IsConjExponent q) (f g : α → ℝ) :
    ⟪f, g⟫ₙ_[ℝ] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by
  cases isEmpty_or_nonempty α
  · simp
  have : 0 < (card α : ℝ) := by positivity
  simpa [nl2Inner_eq_l2Inner_div_card, nlpNorm, div_mul_div_comm, ← rpow_add this,
    hpq.coe.inv_add_inv_conj, div_le_div_right this] using l2Inner_le_lpNorm_mul_lpNorm hpq _ _

/-- **Hölder's inequality**, binary case. -/
lemma abs_nl2Inner_le_nlpNorm_mul_nlpNorm (hpq : p.IsConjExponent q) (f g : α → ℝ) :
    |⟪f, g⟫ₙ_[ℝ]| ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] :=
  abs_nl2Inner_le_nl2Inner_abs.trans $
    (nl2Inner_le_nlpNorm_mul_nlpNorm hpq _ _).trans_eq $ by simp_rw [nlpNorm_abs]

/-- **Hölder's inequality**, binary case. -/
lemma nlpNorm_mul_le (hp : p ≠ 0) (hq : q ≠ 0) (r : ℝ≥0) (hpqr : p⁻¹ + q⁻¹ = r⁻¹) (f g : α → ℝ) :
    ‖f * g‖ₙ_[r] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by
  cases isEmpty_or_nonempty α
  · simp
  have : 0 < (card α : ℝ) := by positivity
  simp only [nl2Inner_eq_l2Inner_div_card, nlpNorm, div_mul_div_comm, ← rpow_add this,
    hpqr, div_le_div_right this, ← NNReal.coe_add, ← NNReal.coe_inv, ENNReal.coe_toReal]
  exact div_le_div_of_nonneg_right (lpNorm_mul_le hp hq _ hpqr _ _) $ by positivity

/-- **Hölder's inequality**, finitary case. -/
lemma nlpNorm_prod_le {s : Finset ι} (hs : s.Nonempty) {p : ι → ℝ≥0} (hp : ∀ i, p i ≠ 0) (q : ℝ≥0)
    (hpq : ∑ i ∈ s, (p i)⁻¹ = q⁻¹) (f : ι → α → ℝ) :
    ‖∏ i ∈ s, f i‖ₙ_[q] ≤ ∏ i ∈ s, ‖f i‖ₙ_[p i] := by
  cases isEmpty_or_nonempty α
  · simp
  have : 0 < (card α : ℝ) := by positivity
  simp only [nl2Inner_eq_l2Inner_div_card, nlpNorm, prod_div_distrib, ← rpow_sum_of_pos this,
    hpq, div_le_div_right this, ← NNReal.coe_sum, ← NNReal.coe_inv, ENNReal.coe_toReal]
  exact div_le_div_of_nonneg_right (lpNorm_prod_le hs hp _ hpq _) $ by positivity

end nlpNorm

/-! ### Indicator -/

section indicate
variable {α β : Type*} [RCLike β] [Fintype α] [DecidableEq α] {s : Finset α} {p : ℝ≥0}

lemma nlpNorm_rpow_indicate (hp : p ≠ 0) (s : Finset α) : ‖𝟭_[β] s‖ₙ_[p] ^ (p : ℝ) = s.dens := by
  rw [nlpNorm, div_rpow]
  simp [lpNorm_rpow_indicate hp, lpNorm_indicate, hp, dens]
  all_goals positivity

lemma nlpNorm_indicate (hp : p ≠ 0) (s : Finset α) : ‖𝟭_[β] s‖ₙ_[p] = s.dens ^ (p⁻¹ : ℝ) := by
  refine (eq_rpow_inv ?_ ?_ ?_).2 (nlpNorm_rpow_indicate ?_ _) <;> positivity

lemma nlpNorm_pow_indicate {p : ℕ} (hp : p ≠ 0) (s : Finset α) :
    ‖𝟭_[β] s‖ₙ_[p] ^ (p : ℝ) = s.dens := by
  simpa using nlpNorm_rpow_indicate (Nat.cast_ne_zero.2 hp) s

lemma nl2Norm_sq_indicate (s : Finset α) : ‖𝟭_[β] s‖ₙ_[2] ^ 2 = s.dens := by
  simpa using nlpNorm_pow_indicate two_ne_zero s

lemma nl2Norm_indicate (s : Finset α) : ‖𝟭_[β] s‖ₙ_[2] = Real.sqrt s.dens := by
  rw [eq_comm, sqrt_eq_iff_sq_eq, nl2Norm_sq_indicate] <;> positivity

@[simp] lemma nl1Norm_indicate (s : Finset α) : ‖𝟭_[β] s‖ₙ_[1] = s.dens := by
  simpa using nlpNorm_pow_indicate one_ne_zero s

end indicate

section mu
variable {α β : Type*} [RCLike β] [Fintype α] [DecidableEq α] {s : Finset α} {p : ℝ≥0}

lemma nlpNorm_mu (hp : 1 ≤ p) (s : Finset α) : ‖μ_[β] s‖ₙ_[p] = s.dens ^ (p⁻¹ : ℝ) / s.card := by
  rw [mu, nlpNorm_smul (ENNReal.one_le_coe_iff.2 hp) (s.card⁻¹ : β) (𝟭_[β] s), nlpNorm_indicate,
      norm_inv, RCLike.norm_natCast, inv_mul_eq_div]; positivity

lemma nl1Norm_mu (s : Finset α) : ‖μ_[β] s‖ₙ_[1] = s.dens / s.card := by
  simpa using nlpNorm_mu le_rfl s

end mu

section
variable {α : Type*} [Fintype α]

@[simp]
lemma RCLike.nlpNorm_coe_comp {𝕜 : Type*} [RCLike 𝕜] (p) (f : α → ℝ) :
    ‖((↑) : ℝ → 𝕜) ∘ f‖ₙ_[p] = ‖f‖ₙ_[p] := by
  simp only [←nlpNorm_norm _ (((↑) : ℝ → 𝕜) ∘ f), ←nlpNorm_norm _ f, Function.comp_apply,
    RCLike.norm_ofReal, Real.norm_eq_abs]

@[simp] lemma Complex.nlpNorm_coe_comp (p) (f : α → ℝ) : ‖((↑) : ℝ → ℂ) ∘ f‖ₙ_[p] = ‖f‖ₙ_[p] :=
  RCLike.nlpNorm_coe_comp _ _

end
