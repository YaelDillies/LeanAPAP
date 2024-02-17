import LeanAPAP.Mathlib.Algebra.BigOperators.Order
import LeanAPAP.Mathlib.Algebra.Order.Group.Abs
import LeanAPAP.Mathlib.Analysis.InnerProductSpace.PiL2
import LeanAPAP.Mathlib.Analysis.NormedSpace.PiLp
import LeanAPAP.Prereqs.Indicator

/-!
# Lp norms
-/

open Finset Function Real
open scoped BigOps ComplexConjugate ENNReal NNReal NNRat

variable {ι 𝕜 : Type*} [Fintype ι]

/-! ### Lp norm -/

section NormedAddCommGroup
variable {α : ι → Type*} [∀ i, NormedAddCommGroup (α i)] {p q : ℝ≥0∞} {f g h : ∀ i, α i}

/-- The Lp norm of a function. -/
noncomputable def lpNorm (p : ℝ≥0∞) (f : ∀ i, α i) : ℝ := ‖(WithLp.equiv p _).symm f‖

notation "‖" f "‖_[" p "]" => lpNorm p f

lemma lpNorm_eq_sum' (hp : p.toReal ≠ 0) (f : ∀ i, α i) :
    ‖f‖_[p] = (∑ i, ‖f i‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  rw [←one_div]; exact PiLp.norm_eq_sum (hp.lt_of_le' ENNReal.toReal_nonneg) _

lemma lpNorm_eq_sum'' {p : ℝ} (hp : 0 < p) (f : ∀ i, α i) :
    ‖f‖_[p.toNNReal] = (∑ i, ‖f i‖ ^ p) ^ p⁻¹ := by rw [lpNorm_eq_sum'] <;>  simp [hp.ne', hp.le]

lemma lpNorm_eq_sum {p : ℝ≥0} (hp : p ≠ 0) (f : ∀ i, α i) :
    ‖f‖_[p] = (∑ i, ‖f i‖ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) := lpNorm_eq_sum' (by simpa using hp) _

lemma lpNorm_rpow_eq_sum {p : ℝ≥0} (hp : p ≠ 0) (f : ∀ i, α i) :
    ‖f‖_[p] ^ (p : ℝ) = ∑ i, ‖f i‖ ^ (p : ℝ) := by
  rw [lpNorm_eq_sum hp, rpow_inv_rpow (sum_nonneg fun i _ ↦ ?_)] <;> positivity

lemma lpNorm_pow_eq_sum {p : ℕ} (hp : p ≠ 0) (f : ∀ i, α i) : ‖f‖_[p] ^ p = ∑ i, ‖f i‖ ^ p := by
  simpa using lpNorm_rpow_eq_sum (Nat.cast_ne_zero.2 hp) f

lemma l2Norm_sq_eq_sum (f : ∀ i, α i) : ‖f‖_[2] ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  simpa using lpNorm_pow_eq_sum two_ne_zero _

lemma l2Norm_eq_sum (f : ∀ i, α i) : ‖f‖_[2] = sqrt (∑ i, ‖f i‖ ^ 2) := by
  simpa [sqrt_eq_rpow] using lpNorm_eq_sum two_ne_zero _

lemma l1Norm_eq_sum (f : ∀ i, α i) : ‖f‖_[1] = ∑ i, ‖f i‖ := by simp [lpNorm_eq_sum']

lemma l0Norm_eq_card (f : ∀ i, α i) : ‖f‖_[0] = {i | f i ≠ 0}.toFinite.toFinset.card :=
  (PiLp.norm_eq_card _).trans $ by simp

lemma linftyNorm_eq_ciSup (f : ∀ i, α i) : ‖f‖_[∞] = ⨆ i, ‖f i‖ := PiLp.norm_eq_ciSup _

@[simp] lemma lpNorm_zero : ‖(0 : ∀ i, α i)‖_[p] = 0 := by
  obtain p | p := p; swap
  obtain rfl | hp := @eq_zero_or_pos _ _ p
  all_goals simp [linftyNorm_eq_ciSup, l0Norm_eq_card, lpNorm_eq_sum, *, ne_of_gt]

@[simp] lemma lpNorm_of_isEmpty [IsEmpty ι] (p : ℝ≥0∞) (f : ∀ i, α i) : ‖f‖_[p] = 0 := by
  simp [Subsingleton.elim f 0]

@[simp] lemma lpNorm_norm (p : ℝ≥0∞) (f : ∀ i, α i) : ‖fun i ↦ ‖f i‖‖_[p] = ‖f‖_[p] := by
  obtain p | p := p; swap
  obtain rfl | hp := @eq_zero_or_pos _ _ p
  all_goals simp [linftyNorm_eq_ciSup, l0Norm_eq_card, lpNorm_eq_sum, *, ne_of_gt]

@[simp] lemma lpNorm_neg (f : ∀ i, α i) : ‖-f‖_[p] = ‖f‖_[p] := by simp [←lpNorm_norm _ (-f)]

lemma lpNorm_sub_comm (f g : ∀ i, α i) : ‖f - g‖_[p] = ‖g - f‖_[p] := by
  simp [←lpNorm_neg (f - g)]

@[simp] lemma lpNorm_nonneg : 0 ≤ ‖f‖_[p] := by
  obtain p | p := p
  · simp only [linftyNorm_eq_ciSup, ENNReal.none_eq_top]
    exact Real.iSup_nonneg fun i ↦ norm_nonneg _
  obtain rfl | hp := eq_or_ne p 0
  · simp only [l0Norm_eq_card, lpNorm_eq_sum, ENNReal.some_eq_coe, ENNReal.coe_zero, *]
    exact Nat.cast_nonneg _
  · simp only [lpNorm_eq_sum hp, ENNReal.some_eq_coe]
    positivity

@[simp] lemma lpNorm_eq_zero : ‖f‖_[p] = 0 ↔ f = 0 := by
  obtain p | p := p
  · cases isEmpty_or_nonempty ι <;>
      simp [linftyNorm_eq_ciSup, ENNReal.none_eq_top, ←sup'_univ_eq_ciSup, le_antisymm_iff,
        Function.funext_iff]
  obtain rfl | hp := eq_or_ne p 0
  · simp [l0Norm_eq_card, eq_empty_iff_forall_not_mem, Function.funext_iff]
  · rw [←rpow_eq_zero lpNorm_nonneg (NNReal.coe_ne_zero.2 hp)]
    simp [lpNorm_rpow_eq_sum hp, sum_eq_zero_iff_of_nonneg, rpow_nonneg, Function.funext_iff,
      rpow_eq_zero _ (NNReal.coe_ne_zero.2 hp)]

@[simp] lemma lpNorm_pos : 0 < ‖f‖_[p] ↔ f ≠ 0 := lpNorm_nonneg.gt_iff_ne.trans lpNorm_eq_zero.not

lemma lpNorm_mono_right (hpq : p ≤ q) (f : ∀ i, α i) : ‖f‖_[p] ≤ ‖f‖_[q] := sorry

section one_le

lemma lpNorm_add_le (hp : 1 ≤ p) (f g : ∀ i, α i) : ‖f + g‖_[p] ≤ ‖f‖_[p] + ‖g‖_[p] :=
  haveI := Fact.mk hp
  norm_add_le _ _

lemma lpNorm_sum_le (hp : 1 ≤ p) {κ : Type*} (s : Finset κ) (f : κ → ∀ i, α i) :
    ‖∑ i ∈ s, f i‖_[p] ≤ ∑ i ∈ s, ‖f i‖_[p] :=
  haveI := Fact.mk hp
  norm_sum_le _ _

lemma lpNorm_sub_le (hp : 1 ≤ p) (f g : ∀ i, α i) : ‖f - g‖_[p] ≤ ‖f‖_[p] + ‖g‖_[p] :=
  haveI := Fact.mk hp
  norm_sub_le _ _

lemma lpNorm_le_lpNorm_add_lpNorm_sub' (hp : 1 ≤ p) (f g : ∀ i, α i) :
    ‖f‖_[p] ≤ ‖g‖_[p] + ‖f - g‖_[p] :=
  haveI := Fact.mk hp
  norm_le_norm_add_norm_sub' _ _

lemma lpNorm_le_lpNorm_add_lpNorm_sub (hp : 1 ≤ p) (f g : ∀ i, α i) :
    ‖f‖_[p] ≤ ‖g‖_[p] + ‖g - f‖_[p] :=
  haveI := Fact.mk hp
  norm_le_norm_add_norm_sub _ _

lemma lpNorm_le_add_lpNorm_add (hp : 1 ≤ p) (f g : ∀ i, α i) : ‖f‖_[p] ≤ ‖f + g‖_[p] + ‖g‖_[p] :=
  haveI := Fact.mk hp
  norm_le_add_norm_add _ _

lemma lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub (hp : 1 ≤ p) (f g : ∀ i, α i) :
    ‖f - h‖_[p] ≤ ‖f - g‖_[p] + ‖g - h‖_[p] :=
  haveI := Fact.mk hp
  norm_sub_le_norm_sub_add_norm_sub _ _ _

variable [NormedField 𝕜] [∀ i, NormedSpace 𝕜 (α i)]

-- TODO: `p ≠ 0` is enough
lemma lpNorm_smul (hp : 1 ≤ p) (c : 𝕜) (f : ∀ i, α i) : ‖c • f‖_[p] = ‖c‖ * ‖f‖_[p] :=
  haveI := Fact.mk hp
  norm_smul c _

variable [∀ i, NormedSpace ℝ (α i)]

lemma lpNorm_nsmul (hp : 1 ≤ p) (n : ℕ) (f : ∀ i, α i) : ‖n • f‖_[p] = n • ‖f‖_[p] :=
  haveI := Fact.mk hp
  IsROrC.norm_nsmul ℝ _ _

lemma lpNorm_expect_le [∀ i, Module ℚ≥0 (α i)] (hp : 1 ≤ p) {κ : Type*} (s : Finset κ) (f : κ → ∀ i, α i) :
    ‖𝔼 i ∈ s, f i‖_[p] ≤ 𝔼 i ∈ s, ‖f i‖_[p] := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  refine (le_inv_smul_iff_of_pos $ by positivity).2 ?_
  rw [← nsmul_eq_smul_cast, ← lpNorm_nsmul hp, card_smul_expect]
  exact lpNorm_sum_le hp _ _

end one_le
end NormedAddCommGroup

section NormedAddCommGroup
variable {α : Type*} [NormedAddCommGroup α] {p : ℝ≥0}

@[simp]
lemma lpNorm_const (hp : p ≠ 0) (a : α) :
    ‖const ι a‖_[p] = (Fintype.card ι : ℝ) ^ (p⁻¹ : ℝ) * ‖a‖ := by
  simp only [lpNorm_eq_sum hp, card_univ, mul_rpow, norm_nonneg, rpow_nonneg,
    NNReal.coe_ne_zero.2 hp, rpow_rpow_inv, const_apply, sum_const, nsmul_eq_mul, Nat.cast_nonneg,
    Ne.def, not_false_iff]

end NormedAddCommGroup

section IsROrC
variable [IsROrC 𝕜] {p : ℝ≥0} {f g : ι → 𝕜}

@[simp] lemma lpNorm_one (hp : p ≠ 0) : ‖(1 : ι → 𝕜)‖_[p] = Fintype.card ι ^ (p⁻¹ : ℝ) :=
  (lpNorm_const hp 1).trans $ by simp

lemma lpNorm_natCast_mul {p : ℝ≥0∞} (hp : 1 ≤ p) (n : ℕ) (f : ι → 𝕜) :
    ‖(n : ι → 𝕜) * f‖_[p] = n * ‖f‖_[p] := by simpa only [nsmul_eq_mul] using lpNorm_nsmul hp n f

lemma lpNorm_natCast_mul' {p : ℝ≥0∞} (hp : 1 ≤ p) (n : ℕ) (f : ι → 𝕜) :
    ‖(n * f ·)‖_[p] = n * ‖f‖_[p] := lpNorm_natCast_mul hp _ _

lemma lpNorm_mul_natCast {p : ℝ≥0∞} (hp : 1 ≤ p) (f : ι → 𝕜) (n : ℕ) :
    ‖f * (n : ι → 𝕜)‖_[p] = ‖f‖_[p] * n := by simpa only [mul_comm] using lpNorm_natCast_mul hp n f

lemma lpNorm_mul_natCast' {p : ℝ≥0∞} (hp : 1 ≤ p) (f : ι → 𝕜) (n : ℕ) :
    ‖(f · * n)‖_[p] = ‖f‖_[p] * n := lpNorm_mul_natCast hp _ _

lemma lpNorm_div_natCast {p : ℝ≥0∞} (hp : 1 ≤ p) (f : ι → 𝕜) (n : ℕ) :
    ‖f / (n : ι → 𝕜)‖_[p] = ‖f‖_[p] / n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp [Function.funext_iff]
  · rw [eq_div_iff (by positivity), ← lpNorm_mul_natCast hp]
    simp [Pi.mul_def, hn.ne']

lemma lpNorm_div_natCast' {p : ℝ≥0∞} (hp : 1 ≤ p) (f : ι → 𝕜) (n : ℕ) :
    ‖(f · / n)‖_[p] = ‖f‖_[p] / n := lpNorm_div_natCast hp _ _

end IsROrC

section Real
variable {p : ℝ≥0} {f g : ι → ℝ}

lemma lpNorm_mono (hf : 0 ≤ f) (hfg : f ≤ g) : ‖f‖_[p] ≤ ‖g‖_[p] := by
  obtain rfl | hp := eq_or_ne p 0
  · simp only [l0Norm_eq_card, ENNReal.some_eq_coe, ENNReal.coe_zero, Nat.cast_le]
    exact
      card_mono
        (Set.Finite.toFinset_mono fun i ↦ mt fun hi ↦ ((hfg i).trans_eq hi).antisymm $ hf i)
  have hp' := hp
  rw [←pos_iff_ne_zero, ←NNReal.coe_pos] at hp
  simp_rw [←rpow_le_rpow_iff lpNorm_nonneg lpNorm_nonneg hp, lpNorm_rpow_eq_sum hp',
    norm_of_nonneg (hf _), norm_of_nonneg (hf.trans hfg _)]
  exact sum_le_sum fun i _ ↦ rpow_le_rpow (hf _) (hfg _) hp.le

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
variable [OrderedCommSemiring 𝕜] [StarOrderedRing 𝕜] {f g : ι → 𝕜}

lemma l2Inner_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[𝕜] :=
  sum_nonneg fun _ _ ↦ mul_nonneg (star_nonneg_iff.2 $ hf _) $ hg _

end OrderedCommSemiring

section LinearOrderedCommRing
variable [LinearOrderedCommRing 𝕜] [StarOrderedRing 𝕜] [TrivialStar 𝕜] {f g : ι → 𝕜}

--TODO: Can we remove the `TrivialStar` assumption?
lemma abs_l2Inner_le_l2Inner_abs : |⟪f, g⟫_[𝕜]| ≤ ⟪|f|, |g|⟫_[𝕜] :=
  (abs_sum_le_sum_abs _ _).trans_eq $
    sum_congr rfl fun i _ ↦ by simp only [abs_mul, conj_trivial, Pi.abs_apply]

end LinearOrderedCommRing

section IsROrC
variable {κ : Type*} [IsROrC 𝕜] {f : ι → 𝕜}

lemma l2Inner_eq_inner (f g : ι → 𝕜) :
    ⟪f, g⟫_[𝕜] = inner ((WithLp.equiv 2 _).symm f) ((WithLp.equiv 2 _).symm g) := rfl

lemma inner_eq_l2Inner (f g : PiLp 2 fun _i : ι ↦ 𝕜) :
    inner f g = ⟪WithLp.equiv 2 _ f, WithLp.equiv 2 _ g⟫_[𝕜] := rfl

@[simp] lemma l2Inner_self (f : ι → 𝕜) : ⟪f, f⟫_[𝕜] = (‖f‖_[2] : 𝕜) ^ 2 := by
  simp_rw [←algebraMap.coe_pow, l2Norm_sq_eq_sum, l2Inner_eq_sum, algebraMap.coe_sum,
    IsROrC.ofReal_pow, IsROrC.conj_mul]

lemma l2Inner_self_of_norm_eq_one (hf : ∀ x, ‖f x‖ = 1) : ⟪f, f⟫_[𝕜] = Fintype.card ι := by
  simp [-l2Inner_self, l2Inner_eq_sum, IsROrC.conj_mul, hf, card_univ]

lemma linearIndependent_of_ne_zero_of_l2Inner_eq_zero {v : κ → ι → 𝕜} (hz : ∀ k, v k ≠ 0)
    (ho : Pairwise fun k l ↦ ⟪v k, v l⟫_[𝕜] = 0) : LinearIndependent 𝕜 v := by
  simp_rw [l2Inner_eq_inner] at ho
  have := linearIndependent_of_ne_zero_of_inner_eq_zero ?_ ho
  exacts [this, hz]

end IsROrC

section lpNorm
variable {α β : Type*} [AddCommGroup α] [Fintype α] {p : ℝ≥0∞}

@[simp]
lemma lpNorm_translate [NormedAddCommGroup β] (a : α) (f : α → β) : ‖τ a f‖_[p] = ‖f‖_[p] := by
  obtain p | p := p
  · simp only [linftyNorm_eq_ciSup, ENNReal.none_eq_top, translate_apply]
    exact (Equiv.subRight _).iSup_congr fun _ ↦ rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [l0Norm_eq_card, translate_apply, Ne.def, ENNReal.some_eq_coe, ENNReal.coe_zero,
      Nat.cast_inj]
    exact
      card_congr (fun x _ ↦ x - a) (fun x hx ↦ by simpa using hx)
        (fun x y _ _ h ↦ by simpa using h) fun x hx ↦ ⟨x + a, by simpa using hx⟩
  · simp only [lpNorm_eq_sum hp, ENNReal.some_eq_coe, translate_apply]
    congr 1
    exact Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl

@[simp] lemma lpNorm_conj [IsROrC β] (f : α → β) : ‖conj f‖_[p] = ‖f‖_[p] := by
  obtain p | p := p; swap; obtain rfl | hp := eq_or_ne p 0
  all_goals
    simp only [linftyNorm_eq_ciSup, lpNorm_eq_sum, l0Norm_eq_card, ENNReal.some_eq_coe,
      ENNReal.none_eq_top, ENNReal.coe_zero, Pi.conj_apply, IsROrC.norm_conj, map_ne_zero, *]
  · simp only [lpNorm_eq_sum hp, Pi.conj_apply, IsROrC.norm_conj]

@[simp] lemma lpNorm_conjneg [IsROrC β] (f : α → β) : ‖conjneg f‖_[p] = ‖f‖_[p] := by
  simp only [conjneg, lpNorm_conj]
  obtain p | p := p
  · simp only [linftyNorm_eq_ciSup, ENNReal.none_eq_top, conjneg, IsROrC.norm_conj]
    exact (Equiv.neg _).iSup_congr fun _ ↦ rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [l0Norm_eq_card, Ne.def, ENNReal.some_eq_coe, ENNReal.coe_zero, Nat.cast_inj]
    exact
      card_congr (fun x _ ↦ -x) (fun x hx ↦ by simpa using hx) (fun x y _ _ ↦ neg_inj.1)
        fun x hx ↦ ⟨-x, by simpa using hx⟩
  · simp only [lpNorm_eq_sum hp, ENNReal.some_eq_coe]
    congr 1
    exact Fintype.sum_equiv (Equiv.neg _) _ _ fun _ ↦ rfl

lemma lpNorm_translate_sum_sub_le [NormedAddCommGroup β] (hp : 1 ≤ p) {ι : Type*} (s : Finset ι)
    (a : ι → α) (f : α → β) : ‖τ (∑ i ∈ s, a i) f - f‖_[p] ≤ ∑ i ∈ s, ‖τ (a i) f - f‖_[p] := by
  induction' s using Finset.cons_induction with i s ih hs
  · simp
  calc
    _ = ‖τ (∑ j ∈ s, a j) (τ (a i) f - f) + (τ (∑ j ∈ s, a j) f - f)‖_[p] := by
        rw [sum_cons, translate_add', translate_sub_right, sub_add_sub_cancel]
    _ ≤ ‖τ (∑ j ∈ s, a j) (τ (a i) f - f)‖_[p] + ‖(τ (∑ j ∈ s, a j) f - f)‖_[p] :=
        lpNorm_add_le hp _ _
    _ ≤ ‖τ (∑ j ∈ s, a j) (τ (a i) f - f)‖_[p] + ∑ j ∈ s, ‖(τ (a j) f - f)‖_[p] :=
        add_le_add_left hs _
    _ = _ := by rw [lpNorm_translate, sum_cons]

end lpNorm

section IsROrC
variable {α β : Type*} [Fintype α]

lemma l1Norm_mul [IsROrC β] (f g : α → β) :
    ‖f * g‖_[1] = ⟪fun i ↦ ‖f i‖, fun i ↦ ‖g i‖⟫_[ℝ] := by simp [l2Inner_eq_sum, l1Norm_eq_sum]

end IsROrC

/-- **Cauchy-Schwarz inequality** -/
lemma l2Inner_le_l2Norm_mul_l2Norm (f g : ι → ℝ) : ⟪f, g⟫_[ℝ] ≤ ‖f‖_[2] * ‖g‖_[2] :=
  real_inner_le_norm ((WithLp.equiv 2 _).symm f) _

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

private alias ⟨_, lpNorm_pos_of_ne_zero⟩ := lpNorm_pos

private lemma lpNorm_pos_of_pos {α : ι → Type*} [∀ i, NormedAddCommGroup (α i)]
    [∀ i, Preorder (α i)] {p : ℝ≥0∞} {f : ∀ i, α i} (hf : 0 < f) : 0 < ‖f‖_[p] :=
  lpNorm_pos_of_ne_zero hf.ne'

section OrderedCommSemiring
variable [OrderedCommSemiring 𝕜] [StarOrderedRing 𝕜] {f g : ι → 𝕜}

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
variable {α : ι → Type*} [∀ i, NormedAddCommGroup (α i)] {w : ι → ℝ≥0} {f : ∀ i, α i}

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
variable [OrderedCommSemiring 𝕜] [StarOrderedRing 𝕜] {f g : ι → 𝕜}

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
  rw [← rpow_natCast_mul lpNorm_nonneg, ← mul_comm, ← ENNReal.coe_nat, ← ENNReal.coe_mul,
    ← NNReal.coe_nat_cast, ←NNReal.coe_mul, lpNorm_rpow_eq_sum hp, lpNorm_rpow_eq_sum]
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
variable {α : Type*} [Fintype α] [IsROrC 𝕜] {p q : ℝ≥0} {f g : α → 𝕜}

lemma lpNorm_eq_l1Norm_rpow (hp : p ≠ 0) (f : α → 𝕜) :
    ‖f‖_[p] = ‖fun a ↦ ‖f a‖ ^ (p : ℝ)‖_[1] ^ (p⁻¹ : ℝ) := by
  simp [lpNorm_eq_sum hp, l1Norm_eq_sum, abs_rpow_of_nonneg]

lemma lpNorm_rpow' (hp : p ≠ 0) (hq : q ≠ 0) (f : α → 𝕜) :
    ‖f‖_[p] ^ (q : ℝ) = ‖(fun a ↦ ‖f a‖) ^ (q : ℝ)‖_[p / q] := by
  rw [←ENNReal.coe_div hq, lpNorm_rpow (div_ne_zero hp hq) hq (fun _ ↦ norm_nonneg _), lpNorm_norm,
    ← ENNReal.coe_mul, div_mul_cancel _ hq]

lemma norm_l2Inner_le (f g : α → 𝕜) : ‖⟪f, g⟫_[𝕜]‖ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫_[ℝ] :=
  (norm_sum_le _ _).trans $ by simp [l2Inner]

/-- **Hölder's inequality**, binary case. -/
lemma norm_l2Inner_le_lpNorm_mul_lpNorm (hpq : p.IsConjExponent q) (f g : α → 𝕜) :
    ‖⟪f, g⟫_[𝕜]‖ ≤ ‖f‖_[p] * ‖g‖_[q] :=
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
  have : (‖(f * g) ·‖ ^ (r : ℝ)) = (‖f ·‖ ^ (r : ℝ)) * (‖g ·‖ ^ (r : ℝ)) := by
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
  refine'
    (lpNorm_mul_le (hp _) (inv_ne_zero (sum_pos (fun _ _ ↦ _) hs).ne') _ hpq _ _).trans
      (mul_le_mul_of_nonneg_left (ih hs _ (inv_inv _).symm) lpNorm_nonneg)
  exact pos_iff_ne_zero.2 (inv_ne_zero $ hp _)

end Hoelder

/-! ### Indicator -/

section indicate
variable {α β : Type*} [IsROrC β] [Fintype α] [DecidableEq α] {s : Finset α} {p : ℝ≥0}

lemma lpNorm_rpow_indicate (hp : p ≠ 0) (s : Finset α) : ‖𝟭_[β] s‖_[p] ^ (p : ℝ) = s.card := by
  have : ∀ x, (ite (x ∈ s) 1 0 : ℝ) ^ (p : ℝ) =
    ite (x ∈ s) ((1 : ℝ) ^ (p : ℝ) : ℝ) ((0 : ℝ) ^ (p : ℝ)) := fun x ↦ by split_ifs <;> simp
  simp [lpNorm_rpow_eq_sum, hp, indicate_apply, apply_ite Norm.norm, -sum_const, card_eq_sum_ones,
    sum_boole, this, zero_rpow, filter_mem_eq_inter]

lemma lpNorm_indicate (hp : p ≠ 0) (s : Finset α) : ‖𝟭_[β] s‖_[p] = s.card ^ (p⁻¹ : ℝ) := by
  refine' (eq_rpow_inv _ _ _).2 (lpNorm_rpow_indicate _ _) <;> positivity

lemma lpNorm_pow_indicate {p : ℕ} (hp : p ≠ 0) (s : Finset α) :
    ‖𝟭_[β] s‖_[p] ^ (p : ℝ) = s.card := by
  simpa using lpNorm_rpow_indicate (Nat.cast_ne_zero.2 hp) s

lemma l2Norm_sq_indicate (s : Finset α) : ‖𝟭_[β] s‖_[2] ^ 2 = s.card := by
  simpa using lpNorm_pow_indicate two_ne_zero s

lemma l2Norm_indicate (s : Finset α) : ‖𝟭_[β] s‖_[2] = Real.sqrt s.card := by
  rw [eq_comm, sqrt_eq_iff_sq_eq, l2Norm_sq_indicate] <;> positivity

@[simp] lemma l1Norm_indicate (s : Finset α) : ‖𝟭_[β] s‖_[1] = s.card := by
  simpa using lpNorm_pow_indicate one_ne_zero s

end indicate

section mu
variable {α β : Type*} [IsROrC β] [Fintype α] [DecidableEq α] {s : Finset α} {p : ℝ≥0}

lemma lpNorm_mu (hp : 1 ≤ p) (hs : s.Nonempty) : ‖μ_[β] s‖_[p] = s.card ^ ((p : ℝ)⁻¹ - 1) := by
  rw [mu, lpNorm_smul (ENNReal.one_le_coe_iff.2 hp) (s.card⁻¹ : β) (𝟭_[β] s), lpNorm_indicate,
      norm_inv, IsROrC.norm_natCast, inv_mul_eq_div, ←rpow_sub_one] <;> positivity

lemma lpNorm_mu_le (hp : 1 ≤ p) : ‖μ_[β] s‖_[p] ≤ s.card ^ (p⁻¹ - 1 : ℝ) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
    positivity
  · exact (lpNorm_mu hp hs).le

lemma l1Norm_mu (hs : s.Nonempty) : ‖μ_[β] s‖_[1] = 1 := by simpa using lpNorm_mu le_rfl hs

lemma l1Norm_mu_le_one : ‖μ_[β] s‖_[1] ≤ 1 := by simpa using lpNorm_mu_le le_rfl

end mu

section
variable {α : Type*} [Fintype α]

@[simp]
lemma IsROrC.lpNorm_coe_comp {𝕜 : Type*} [IsROrC 𝕜] (p) (f : α → ℝ) :
    ‖((↑) : ℝ → 𝕜) ∘ f‖_[p] = ‖f‖_[p] := by
  simp only [←lpNorm_norm _ (((↑) : ℝ → 𝕜) ∘ f), ←lpNorm_norm _ f, Function.comp_apply,
    IsROrC.norm_ofReal, Real.norm_eq_abs]

@[simp] lemma Complex.lpNorm_coe_comp (p) (f : α → ℝ) : ‖((↑) : ℝ → ℂ) ∘ f‖_[p] = ‖f‖_[p] :=
  IsROrC.lpNorm_coe_comp _ _

end
