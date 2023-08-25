import Project.Mathlib.Algebra.Order.LatticeGroup
import Project.Mathlib.Analysis.InnerProductSpace.PiL2
import Project.Mathlib.Analysis.Normed.Group.Basic
import Project.Mathlib.Analysis.NormedSpace.PiLp
import Project.Mathlib.Analysis.NormedSpace.Ray
import Project.Mathlib.Analysis.SpecialFunctions.Pow.Real
import Project.Mathlib.Data.Real.Basic
import Project.Mathlib.Data.Real.Ennreal
import Project.Mathlib.Data.Real.Nnreal
import Project.Mathlib.Order.ConditionallyCompleteLattice.Finset
import Project.Prereqs.Indicator

#align_import prereqs.lp_norm

/-!
# Lp norms
-/


open Finset Function Real

open scoped BigOperators ComplexConjugate ENNReal NNReal

variable {ι 𝕜 : Type _} [Fintype ι]

/-! ### Lp norm -/


section NormedAddCommGroup

variable {α : ι → Type _} [∀ i, NormedAddCommGroup (α i)] {p q : ℝ≥0∞} {f g h : ∀ i, α i}

/-- The Lp norm of a function. -/
noncomputable def lpnorm (p : ℝ≥0∞) (f : ∀ i, α i) : ℝ :=
  ‖(PiLp.equiv p _).symm f‖

notation "‖" f "‖_[" p "]" => lpnorm p f

theorem lpnorm_eq_sum' (hp : p.toReal ≠ 0) (f : ∀ i, α i) :
    ‖f‖_[p] = (∑ i, ‖f i‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  rw [← one_div] <;> exact PiLp.norm_eq_sum (hp.lt_of_le' ENNReal.toReal_nonneg) _

theorem lpnorm_eq_sum'' {p : ℝ} (hp : 0 < p) (f : ∀ i, α i) :
    ‖f‖_[p.toNNReal] = (∑ i, ‖f i‖ ^ p) ^ p⁻¹ := by rw [lpnorm_eq_sum'] <;> simp [hp.ne', hp.le]

theorem lpnorm_eq_sum {p : ℝ≥0} (hp : p ≠ 0) (f : ∀ i, α i) :
    ‖f‖_[p] = (∑ i, ‖f i‖ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) :=
  lpnorm_eq_sum' (by simpa using hp) _

theorem lpnorm_rpow_eq_sum {p : ℝ≥0} (hp : p ≠ 0) (f : ∀ i, α i) :
    ‖f‖_[p] ^ (p : ℝ) = ∑ i, ‖f i‖ ^ (p : ℝ) :=
  by
  rw [lpnorm_eq_sum hp, rpow_inv_rpow]
  · exact sum_nonneg fun i _ => by positivity
  · positivity

theorem lpnorm_pow_eq_sum {p : ℕ} (hp : p ≠ 0) (f : ∀ i, α i) : ‖f‖_[p] ^ p = ∑ i, ‖f i‖ ^ p := by
  simpa using lpnorm_rpow_eq_sum (Nat.cast_ne_zero.2 hp) f

theorem L2norm_sq_eq_sum (f : ∀ i, α i) : ‖f‖_[2] ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  simpa using lpnorm_pow_eq_sum two_ne_zero _

theorem L2norm_eq_sum (f : ∀ i, α i) : ‖f‖_[2] = sqrt (∑ i, ‖f i‖ ^ 2) := by
  simpa [sqrt_eq_rpow] using lpnorm_eq_sum two_ne_zero _

theorem L1norm_eq_sum (f : ∀ i, α i) : ‖f‖_[1] = ∑ i, ‖f i‖ := by simp [lpnorm_eq_sum']

theorem L0norm_eq_card (f : ∀ i, α i) : ‖f‖_[0] = {i | f i ≠ 0}.toFinite.toFinset.card :=
  PiLp.norm_eq_card _

theorem Linftynorm_eq_csupr (f : ∀ i, α i) : ‖f‖_[∞] = ⨆ i, ‖f i‖ :=
  PiLp.norm_eq_ciSup _

@[simp]
theorem lpnorm_zero : ‖(0 : ∀ i, α i)‖_[p] = 0 :=
  by
  cases p; swap
  obtain rfl | hp := @eq_zero_or_pos _ _ p
  all_goals simp [Linftynorm_eq_csupr, L0norm_eq_card, lpnorm_eq_sum, *, ne_of_gt]

@[simp]
theorem lpnorm_norm (p : ℝ≥0∞) (f : ∀ i, α i) : ‖fun i => ‖f i‖‖_[p] = ‖f‖_[p] :=
  by
  cases p; swap
  obtain rfl | hp := @eq_zero_or_pos _ _ p
  all_goals simp [Linftynorm_eq_csupr, L0norm_eq_card, lpnorm_eq_sum, *, ne_of_gt]

@[simp]
theorem lpnorm_neg (f : ∀ i, α i) : ‖-f‖_[p] = ‖f‖_[p] := by simp [← lpnorm_norm _ (-f)]

theorem lpnorm_sub_comm (f g : ∀ i, α i) : ‖f - g‖_[p] = ‖g - f‖_[p] := by
  simp [← lpnorm_neg (f - g)]

@[simp]
theorem lpnorm_nonneg : 0 ≤ ‖f‖_[p] := by
  cases p
  · simp only [Linftynorm_eq_csupr, ENNReal.none_eq_top]
    exact Real.iSup_nonneg fun i => norm_nonneg _
  obtain rfl | hp := eq_or_ne p 0
  · simp only [L0norm_eq_card, ENNReal.some_eq_coe, ENNReal.coe_zero]
    exact Nat.cast_nonneg _
  · simp only [lpnorm_eq_sum hp, ENNReal.some_eq_coe]
    exact rpow_nonneg (sum_nonneg fun i _ => rpow_nonneg <| norm_nonneg _)

@[simp]
theorem lpnorm_eq_zero : ‖f‖_[p] = 0 ↔ f = 0 :=
  by
  cases p
  ·
    cases isEmpty_or_nonempty ι <;>
      simp [Linftynorm_eq_csupr, ENNReal.none_eq_top, ← sup'_univ_eq_csupr, le_antisymm_iff,
        Function.funext_iff]
  obtain rfl | hp := eq_or_ne p 0
  · simp [L0norm_eq_card, eq_empty_iff_forall_not_mem, Function.funext_iff]
  · rw [← rpow_eq_zero lpnorm_nonneg (NNReal.coe_ne_zero.2 hp)]
    simp [lpnorm_rpow_eq_sum hp, sum_eq_zero_iff_of_nonneg, rpow_nonneg, Function.funext_iff,
      rpow_eq_zero _ (NNReal.coe_ne_zero.2 hp)]

@[simp]
theorem lpnorm_pos : 0 < ‖f‖_[p] ↔ f ≠ 0 :=
  lpnorm_nonneg.gt_iff_ne.trans lpnorm_eq_zero.Not

theorem lpnorm_mono_right (hpq : p ≤ q) (f : ∀ i, α i) : ‖f‖_[p] ≤ ‖f‖_[q] :=
  sorry

section one_le

theorem lpnorm_add_le (hp : 1 ≤ p) (f g : ∀ i, α i) : ‖f + g‖_[p] ≤ ‖f‖_[p] + ‖g‖_[p] :=
  haveI := Fact.mk hp
  norm_add_le _ _

theorem lpnorm_sub_le (hp : 1 ≤ p) (f g : ∀ i, α i) : ‖f - g‖_[p] ≤ ‖f‖_[p] + ‖g‖_[p] :=
  haveI := Fact.mk hp
  norm_sub_le _ _

theorem lpnorm_le_lpnorm_add_lpnorm_sub' (hp : 1 ≤ p) (f g : ∀ i, α i) :
    ‖f‖_[p] ≤ ‖g‖_[p] + ‖f - g‖_[p] :=
  haveI := Fact.mk hp
  norm_le_norm_add_norm_sub' _ _

theorem lpnorm_le_lpnorm_add_lpnorm_sub (hp : 1 ≤ p) (f g : ∀ i, α i) :
    ‖f‖_[p] ≤ ‖g‖_[p] + ‖g - f‖_[p] :=
  haveI := Fact.mk hp
  norm_le_norm_add_norm_sub _ _

theorem lpnorm_le_add_lpnorm_add (hp : 1 ≤ p) (f g : ∀ i, α i) : ‖f‖_[p] ≤ ‖f + g‖_[p] + ‖g‖_[p] :=
  haveI := Fact.mk hp
  norm_le_add_norm_add _ _

theorem lpnorm_sub_le_lpnorm_sub_add_lpnorm_sub (hp : 1 ≤ p) :
    ‖f - h‖_[p] ≤ ‖f - g‖_[p] + ‖g - h‖_[p] :=
  haveI := Fact.mk hp
  norm_sub_le_norm_sub_add_norm_sub

variable [NormedField 𝕜] [∀ i, NormedSpace 𝕜 (α i)]

-- TODO: `p ≠ 0` is enough
theorem lpnorm_smul (hp : 1 ≤ p) (c : 𝕜) (f : ∀ i, α i) : ‖c • f‖_[p] = ‖c‖ * ‖f‖_[p] :=
  haveI := Fact.mk hp
  norm_smul _ _

-- TODO: Why is it so hard to use `Lpnorm_smul` directly? `function.has_smul` seems to have a hard
-- time unifying `pi.has_smul`
theorem lpnorm_smul' {α : Type _} [NormedAddCommGroup α] [NormedSpace 𝕜 α] (hp : 1 ≤ p) (c : 𝕜)
    (f : ι → α) : ‖c • f‖_[p] = ‖c‖ * ‖f‖_[p] :=
  lpnorm_smul hp _ _

variable [∀ i, NormedSpace ℝ (α i)]

theorem lpnorm_nsmul (hp : 1 ≤ p) (n : ℕ) (f : ∀ i, α i) : ‖n • f‖_[p] = n • ‖f‖_[p] :=
  haveI := Fact.mk hp
  norm_nsmul _ _

-- TODO: Why is it so hard to use `Lpnorm_nsmul` directly? `function.has_smul` seems to have a hard
-- time unifying `pi.has_smul`
theorem lpnorm_nsmul' {α : Type _} [NormedAddCommGroup α] [NormedSpace ℝ α] (hp : 1 ≤ p) (n : ℕ)
    (f : ι → α) : ‖n • f‖_[p] = n • ‖f‖_[p] :=
  lpnorm_nsmul hp _ _

end one_le

end NormedAddCommGroup

section Real

variable {p : ℝ≥0} {f g : ι → ℝ}

@[simp]
theorem lpnorm_one (hp : p ≠ 0) : ‖(1 : ι → ℝ)‖_[p] = Fintype.card ι ^ (p⁻¹ : ℝ) := by
  simp [lpnorm_eq_sum hp, card_univ]

theorem lpnorm_mono (hf : 0 ≤ f) (hfg : f ≤ g) : ‖f‖_[p] ≤ ‖g‖_[p] :=
  by
  obtain rfl | hp := eq_or_ne p 0
  · simp only [L0norm_eq_card, ENNReal.some_eq_coe, ENNReal.coe_zero, Nat.cast_le]
    exact
      card_mono
        (Set.Finite.toFinset_mono fun i => mt fun hi => ((hfg i).trans_eq hi).antisymm <| hf i)
  have hp' := hp
  rw [← pos_iff_ne_zero, ← NNReal.coe_pos] at hp 
  simp_rw [← rpow_le_rpow_iff lpnorm_nonneg lpnorm_nonneg hp, lpnorm_rpow_eq_sum hp',
    norm_of_nonneg (hf _), norm_of_nonneg (hf.trans hfg _)]
  exact sum_le_sum fun i _ => rpow_le_rpow (hf _) (hfg _) hp.le

end Real

/-! #### Weighted Lp norm -/


section NormedAddCommGroup

variable {α : ι → Type _} [∀ i, NormedAddCommGroup (α i)] {p q : ℝ≥0} {w : ι → ℝ≥0}
  {f g h : ∀ i, α i}

/-- The weighted Lp norm of a function. -/
noncomputable def wLpnorm (p : ℝ≥0) (w : ι → ℝ≥0) (f : ∀ i, α i) : ℝ :=
  ‖fun i => w i ^ (p⁻¹ : ℝ) • ‖f i‖‖_[p]

notation "‖" f "‖_[" p ", " w "]" => wLpnorm p w f

@[simp]
theorem wLpnorm_one_eq_lpnorm (p : ℝ≥0) (f : ∀ i, α i) : ‖f‖_[p, 1] = ‖f‖_[p] := by
  obtain rfl | hp := @eq_zero_or_pos _ _ p <;> simp [wLpnorm, L0norm_eq_card, lpnorm_eq_sum, *]

@[simp]
theorem wLpnorm_const_right (hp : 1 ≤ p) (w : ℝ≥0) (f : ∀ i, α i) :
    ‖f‖_[p, const _ w] = w ^ (p⁻¹ : ℝ) * ‖f‖_[p] := by
  simpa [wLpnorm, -norm_eq_abs, norm_of_nonneg, Pi.smul_def, NNReal.smul_def, rpow_nonneg] using
    lpnorm_smul (ENNReal.one_le_coe_iff.2 hp) (w ^ (p⁻¹ : ℝ) : ℝ) fun i => ‖f i‖

theorem wLpnorm_eq_sum (hp : p ≠ 0) (w : ι → ℝ≥0) (f : ∀ i, α i) :
    ‖f‖_[p, w] = (∑ i, w i • ‖f i‖ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) :=
  by
  have : (p : ℝ) ≠ 0 := by positivity
  simp_rw [wLpnorm, lpnorm_eq_sum hp, NNReal.smul_def, norm_smul]
  simp only [NNReal.coe_rpow, norm_norm, Algebra.id.smul_eq_mul, mul_rpow, norm_nonneg,
    rpow_nonneg_of_nonneg, hp, NNReal.coe_nonneg, norm_of_nonneg, rpow_inv_rpow _ this]

theorem wLpnorm_eq_sum' {p : ℝ} (hp : 0 < p) (w : ι → ℝ≥0) (f : ∀ i, α i) :
    ‖f‖_[p.toNNReal, w] = (∑ i, w i • ‖f i‖ ^ p) ^ p⁻¹ := by
  rw [wLpnorm_eq_sum] <;> simp [hp, hp.ne', hp.le]

theorem wLpnorm_rpow_eq_sum {p : ℝ≥0} (hp : p ≠ 0) (w : ι → ℝ≥0) (f : ∀ i, α i) :
    ‖f‖_[p, w] ^ (p : ℝ) = ∑ i, w i • ‖f i‖ ^ (p : ℝ) :=
  by
  rw [wLpnorm_eq_sum hp, rpow_inv_rpow]
  · exact sum_nonneg fun i _ => by positivity
  · positivity

theorem wLpnorm_pow_eq_sum {p : ℕ} (hp : p ≠ 0) (w : ι → ℝ≥0) (f : ∀ i, α i) :
    ‖f‖_[p, w] ^ p = ∑ i, w i • ‖f i‖ ^ p := by
  simpa using wLpnorm_rpow_eq_sum (Nat.cast_ne_zero.2 hp) w f

theorem wL1norm_eq_sum (w : ι → ℝ≥0) (w : ι → ℝ≥0) (f : ∀ i, α i) : ‖f‖_[1, w] = ∑ i, w i • ‖f i‖ :=
  by simp [wLpnorm_eq_sum]

theorem wL0norm_eq_card (w : ι → ℝ≥0) (f : ∀ i, α i) :
    ‖f‖_[0, w] = {i | f i ≠ 0}.toFinite.toFinset.card := by simp [wLpnorm, L0norm_eq_card]

@[simp]
theorem wLpnorm_zero (w : ι → ℝ≥0) : ‖(0 : ∀ i, α i)‖_[p, w] = 0 := by simp [wLpnorm, ← Pi.zero_def]

@[simp]
theorem wLpnorm_norm (w : ι → ℝ≥0) (f : ∀ i, α i) : ‖fun i => ‖f i‖‖_[p, w] = ‖f‖_[p, w] := by
  obtain rfl | hp := @eq_zero_or_pos _ _ p <;> simp [wL0norm_eq_card, wLpnorm_eq_sum, *, ne_of_gt]

@[simp]
theorem wLpnorm_neg (w : ι → ℝ≥0) (f : ∀ i, α i) : ‖-f‖_[p, w] = ‖f‖_[p, w] := by
  simp [← wLpnorm_norm _ (-f)]

theorem wLpnorm_sub_comm (w : ι → ℝ≥0) (f g : ∀ i, α i) : ‖f - g‖_[p, w] = ‖g - f‖_[p, w] := by
  simp [← wLpnorm_neg _ (f - g)]

@[simp]
theorem wLpnorm_nonneg : 0 ≤ ‖f‖_[p, w] :=
  lpnorm_nonneg

theorem wLpnorm_mono_right (hpq : p ≤ q) (w : ι → ℝ≥0) (f : ∀ i, α i) : ‖f‖_[p, w] ≤ ‖f‖_[q, w] :=
  sorry

section one_le

theorem wLpnorm_add_le (hp : 1 ≤ p) (w : ι → ℝ≥0) (f g : ∀ i, α i) :
    ‖f + g‖_[p, w] ≤ ‖f‖_[p, w] + ‖g‖_[p, w] :=
  by
  unfold wLpnorm
  refine'
    (lpnorm_add_le (by exact_mod_cast hp) _ _).trans'
      (lpnorm_mono (fun i => by dsimp <;> positivity) fun i => _)
  dsimp
  rw [← smul_add]
  exact smul_le_smul_of_nonneg (norm_add_le _ _) (zero_le _)

theorem wLpnorm_sub_le (hp : 1 ≤ p) (w : ι → ℝ≥0) (f g : ∀ i, α i) :
    ‖f - g‖_[p, w] ≤ ‖f‖_[p, w] + ‖g‖_[p, w] := by
  simpa [sub_eq_add_neg] using wLpnorm_add_le hp w f (-g)

theorem wLpnorm_le_wLpnorm_add_wLpnorm_sub' (hp : 1 ≤ p) (w : ι → ℝ≥0) (f g : ∀ i, α i) :
    ‖f‖_[p, w] ≤ ‖g‖_[p, w] + ‖f - g‖_[p, w] := by simpa using wLpnorm_add_le hp w g (f - g)

theorem wLpnorm_le_wLpnorm_add_wLpnorm_sub (hp : 1 ≤ p) (w : ι → ℝ≥0) (f g : ∀ i, α i) :
    ‖f‖_[p, w] ≤ ‖g‖_[p, w] + ‖g - f‖_[p, w] := by
  rw [wLpnorm_sub_comm] <;> exact wLpnorm_le_wLpnorm_add_wLpnorm_sub' hp _ _ _

theorem wLpnorm_le_add_wLpnorm_add (hp : 1 ≤ p) (w : ι → ℝ≥0) (f g : ∀ i, α i) :
    ‖f‖_[p, w] ≤ ‖f + g‖_[p, w] + ‖g‖_[p, w] := by simpa using wLpnorm_add_le hp w (f + g) (-g)

theorem wLpnorm_sub_le_Lpnorm_sub_add_Lpnorm_sub (hp : 1 ≤ p) :
    ‖f - h‖_[p, w] ≤ ‖f - g‖_[p, w] + ‖g - h‖_[p, w] := by
  simpa using wLpnorm_add_le hp w (f - g) (g - h)

variable [NormedField 𝕜] [∀ i, NormedSpace 𝕜 (α i)]

-- TODO: `p ≠ 0` is enough
theorem wLpnorm_smul (hp : 1 ≤ p) (c : 𝕜) (f : ∀ i, α i) : ‖c • f‖_[p, w] = ‖c‖ * ‖f‖_[p, w] :=
  by
  rw [wLpnorm, wLpnorm]
  have : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  have := lpnorm_smul this ‖c‖ fun i => w i ^ (p⁻¹ : ℝ) • ‖f i‖
  rw [norm_norm] at this 
  rw [← this]
  congr with i : 1
  simp only [Pi.smul_apply, Algebra.id.smul_eq_mul, Algebra.mul_smul_comm, norm_smul]

@[simp]
theorem wLpnorm_smul_right (hp : p ≠ 0) (c : ℝ≥0) (f : ∀ i, α i) :
    ‖f‖_[p, c • w] = c ^ (p⁻¹ : ℝ) * ‖f‖_[p, w] :=
  by
  simp only [wLpnorm_eq_sum hp, NNReal.smul_def, Pi.smul_apply, Algebra.id.smul_eq_mul,
    NNReal.coe_mul, mul_assoc, ← mul_sum]
  exact mul_rpow (by positivity) (sum_nonneg fun _ _ => by positivity)

-- TODO: Why is it so hard to use `wLpnorm_smul` directly? `function.has_smul` seems to have a hard
-- time unifying `pi.has_smul`
theorem wLpnorm_smul' {α : Type _} [NormedAddCommGroup α] [NormedSpace 𝕜 α] (hp : 1 ≤ p) (c : 𝕜)
    (f : ι → α) : ‖c • f‖_[p, w] = ‖c‖ * ‖f‖_[p, w] :=
  wLpnorm_smul hp _ _

variable [∀ i, NormedSpace ℝ (α i)]

theorem wLpnorm_nsmul (hp : 1 ≤ p) (n : ℕ) (w : ι → ℝ≥0) (f : ∀ i, α i) :
    ‖n • f‖_[p, w] = n • ‖f‖_[p, w] := by
  rw [nsmul_eq_smul_cast ℝ, wLpnorm_smul hp, IsROrC.norm_natCast, nsmul_eq_mul]

-- TODO: Why is it so hard to use `wLpnorm_nsmul` directly? `function.has_smul` seems to have a hard
-- time unifying `pi.has_smul`
theorem wLpnorm_nsmul' {α : Type _} [NormedAddCommGroup α] [NormedSpace ℝ α] (hp : 1 ≤ p) (n : ℕ)
    (w : ι → ℝ≥0) (f : ι → α) : ‖n • f‖_[p, w] = n • ‖f‖_[p, w] :=
  wLpnorm_nsmul hp _ _ _

end one_le

end NormedAddCommGroup

section NormedAddCommGroup

variable {α : Type _} [NormedAddCommGroup α] {p : ℝ≥0}

@[simp]
theorem lpnorm_const (hp : p ≠ 0) (a : α) : ‖const ι a‖_[p] = ↑(Fintype.card ι) ^ (p⁻¹ : ℝ) * ‖a‖ :=
  by
  simp only [lpnorm_eq_sum hp, card_univ, mul_rpow, norm_nonneg, rpow_nonneg,
    NNReal.coe_ne_zero.2 hp, rpow_rpow_inv, const_apply, sum_const, nsmul_eq_mul, Nat.cast_nonneg,
    Ne.def, not_false_iff]

end NormedAddCommGroup

section Real

variable {p : ℝ≥0} {w : ι → ℝ≥0} {f g : ι → ℝ}

@[simp]
theorem wLpnorm_one (hp : p ≠ 0) (w : ι → ℝ≥0) : ‖(1 : ι → ℝ)‖_[p, w] = (∑ i, w i) ^ (p⁻¹ : ℝ) := by
  simp [wLpnorm_eq_sum hp, NNReal.smul_def]

theorem wLpnorm_mono (hf : 0 ≤ f) (hfg : f ≤ g) : ‖f‖_[p, w] ≤ ‖g‖_[p, w] :=
  lpnorm_mono (fun i => by dsimp <;> positivity) fun i =>
    smul_le_smul_of_nonneg
        (by rw [norm_of_nonneg (hf _), norm_of_nonneg (hf.trans hfg _)] <;> exact hfg _) <|
      by positivity

end Real

/-! #### Inner product -/


section CommSemiring

variable [CommSemiring 𝕜] [StarRing 𝕜] {γ : Type _} [DistribSMul γ 𝕜]

/-- Inner product giving rise to the L2 norm. -/
def l2inner (f g : ι → 𝕜) : 𝕜 :=
  ∑ i, conj (f i) * g i

notation "⟪" f ", " g "⟫_[" 𝕜 "]" => @l2inner _ 𝕜 _ _ _ f g

theorem l2inner_eq_sum (f g : ι → 𝕜) : ⟪f, g⟫_[𝕜] = ∑ i, conj (f i) * g i :=
  rfl

@[simp]
theorem conj_l2inner (f g : ι → 𝕜) : conj ⟪f, g⟫_[𝕜] = ⟪g, f⟫_[𝕜] := by
  simp [l2inner_eq_sum, map_sum, mul_comm]

@[simp]
theorem l2inner_zero_left (g : ι → 𝕜) : ⟪0, g⟫_[𝕜] = 0 := by simp [l2inner_eq_sum]

@[simp]
theorem l2inner_zero_right (f : ι → 𝕜) : ⟪f, 0⟫_[𝕜] = 0 := by simp [l2inner_eq_sum]

@[simp]
theorem l2inner_const_left (a : 𝕜) (f : ι → 𝕜) : ⟪const _ a, f⟫_[𝕜] = conj a * ∑ x, f x := by
  simp only [l2inner_eq_sum, const_apply, mul_sum]

@[simp]
theorem l2inner_const_right (f : ι → 𝕜) (a : 𝕜) : ⟪f, const _ a⟫_[𝕜] = (∑ x, conj (f x)) * a := by
  simp only [l2inner_eq_sum, const_apply, sum_mul]

theorem l2inner_add_left (f₁ f₂ g : ι → 𝕜) : ⟪f₁ + f₂, g⟫_[𝕜] = ⟪f₁, g⟫_[𝕜] + ⟪f₂, g⟫_[𝕜] := by
  simp_rw [l2inner_eq_sum, Pi.add_apply, map_add, add_mul, sum_add_distrib]

theorem l2inner_add_right (f g₁ g₂ : ι → 𝕜) : ⟪f, g₁ + g₂⟫_[𝕜] = ⟪f, g₁⟫_[𝕜] + ⟪f, g₂⟫_[𝕜] := by
  simp_rw [l2inner_eq_sum, Pi.add_apply, mul_add, sum_add_distrib]

theorem l2inner_smul_left [Star γ] [StarModule γ 𝕜] [IsScalarTower γ 𝕜 𝕜] (c : γ) (f g : ι → 𝕜) :
    ⟪c • f, g⟫_[𝕜] = star c • ⟪f, g⟫_[𝕜] := by
  simp only [l2inner_eq_sum, Pi.smul_apply, smul_mul_assoc, smul_sum, starRingEnd_apply, star_smul]

theorem l2inner_smul_right [Star γ] [StarModule γ 𝕜] [SMulCommClass γ 𝕜 𝕜] (c : γ) (f g : ι → 𝕜) :
    ⟪f, c • g⟫_[𝕜] = c • ⟪f, g⟫_[𝕜] := by
  simp only [l2inner_eq_sum, Pi.smul_apply, mul_smul_comm, smul_sum, starRingEnd_apply, star_smul]

theorem smul_l2inner_left [InvolutiveStar γ] [StarModule γ 𝕜] [IsScalarTower γ 𝕜 𝕜] (c : γ)
    (f g : ι → 𝕜) : c • ⟪f, g⟫_[𝕜] = ⟪star c • f, g⟫_[𝕜] := by rw [l2inner_smul_left, star_star]

end CommSemiring

section CommRing

variable [CommRing 𝕜] [StarRing 𝕜]

theorem l2inner_neg_left (f g : ι → 𝕜) : ⟪-f, g⟫_[𝕜] = -⟪f, g⟫_[𝕜] := by
  simp [l2inner_eq_sum, sum_add_distrib]

theorem l2inner_neg_right (f g : ι → 𝕜) : ⟪f, -g⟫_[𝕜] = -⟪f, g⟫_[𝕜] := by
  simp [l2inner_eq_sum, sum_add_distrib]

theorem l2inner_sub_left (f₁ f₂ g : ι → 𝕜) : ⟪f₁ - f₂, g⟫_[𝕜] = ⟪f₁, g⟫_[𝕜] - ⟪f₂, g⟫_[𝕜] := by
  simp_rw [sub_eq_add_neg, l2inner_add_left, l2inner_neg_left]

theorem l2inner_sub_right (f g₁ g₂ : ι → 𝕜) : ⟪f, g₁ - g₂⟫_[𝕜] = ⟪f, g₁⟫_[𝕜] - ⟪f, g₂⟫_[𝕜] := by
  simp_rw [sub_eq_add_neg, l2inner_add_right, l2inner_neg_right]

end CommRing

section OrderedCommSemiring

variable [OrderedCommSemiring 𝕜] [StarOrderedRing 𝕜] {f g : ι → 𝕜}

theorem l2inner_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[𝕜] :=
  sum_nonneg fun _ _ => mul_nonneg (star_nonneg.2 <| hf _) <| hg _

end OrderedCommSemiring

section LinearOrderedCommRing

variable [LinearOrderedCommRing 𝕜] [StarOrderedRing 𝕜] [TrivialStar 𝕜] {f g : ι → 𝕜}

--TODO: Can we remove the `has_trivial_star` assumption?
theorem abs_l2inner_le_l2inner_abs : |⟪f, g⟫_[𝕜]| ≤ ⟪|f|, |g|⟫_[𝕜] :=
  (abs_sum_le_sum_abs _ _).trans_eq <|
    sum_congr rfl fun i _ => by simp only [abs_mul, conj_trivial, Pi.abs_apply]

end LinearOrderedCommRing

section IsROrC

variable {κ : Type _} [IsROrC 𝕜] {f : ι → 𝕜}

theorem l2inner_eq_inner (f g : ι → 𝕜) :
    ⟪f, g⟫_[𝕜] = inner ((PiLp.equiv 2 _).symm f) ((PiLp.equiv 2 _).symm g) :=
  rfl

theorem inner_eq_l2inner (f g : PiLp 2 fun i : ι => 𝕜) :
    inner f g = ⟪PiLp.equiv 2 _ f, PiLp.equiv 2 _ g⟫_[𝕜] :=
  rfl

@[simp]
theorem l2inner_self (f : ι → 𝕜) : ⟪f, f⟫_[𝕜] = ‖f‖_[2] ^ 2 := by
  simp_rw [← algebraMap.coe_pow, L2norm_sq_eq_sum, l2inner_eq_sum, algebraMap.coe_sum,
    IsROrC.conj_mul, IsROrC.normSq_eq_def']

theorem l2inner_self_of_norm_eq_one (hf : ∀ x, ‖f x‖ = 1) : ⟪f, f⟫_[𝕜] = Fintype.card ι := by
  simp [l2inner_eq_sum, IsROrC.conj_mul, IsROrC.normSq_eq_def', hf, card_univ]

theorem linearIndependent_of_ne_zero_of_l2inner_eq_zero {v : κ → ι → 𝕜} (hz : ∀ k, v k ≠ 0)
    (ho : Pairwise fun k l => ⟪v k, v l⟫_[𝕜] = 0) : LinearIndependent 𝕜 v :=
  by
  simp_rw [l2inner_eq_inner] at ho 
  have := linearIndependent_of_ne_zero_of_inner_eq_zero _ ho
  exacts [this, hz]

end IsROrC

section lpnorm

variable {α β : Type _} [AddCommGroup α] [Fintype α] {p : ℝ≥0∞}

@[simp]
theorem lpnorm_translate [NormedAddCommGroup β] (a : α) (f : α → β) : ‖τ a f‖_[p] = ‖f‖_[p] :=
  by
  cases p
  · simp only [Linftynorm_eq_csupr, ENNReal.none_eq_top, translate_apply]
    exact (Equiv.subRight _).iSup_congr fun _ => rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [L0norm_eq_card, translate_apply, Ne.def, ENNReal.some_eq_coe, ENNReal.coe_zero,
      Nat.cast_inj]
    exact
      card_congr (fun x _ => x - a) (fun x hx => by simpa using hx)
        (fun x y _ _ h => by simpa using h) fun x hx => ⟨x + a, by simpa using hx⟩
  · simp only [lpnorm_eq_sum hp, ENNReal.some_eq_coe, translate_apply]
    congr 1
    exact Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ => rfl

@[simp]
theorem lpnorm_conj [IsROrC β] (f : α → β) : ‖conj f‖_[p] = ‖f‖_[p] :=
  by
  cases p; swap; obtain rfl | hp := eq_or_ne p 0
  all_goals
    simp only [Linftynorm_eq_csupr, lpnorm_eq_sum, L0norm_eq_card, ENNReal.some_eq_coe,
      ENNReal.none_eq_top, ENNReal.coe_zero, Pi.conj_apply, IsROrC.norm_conj, map_ne_zero, *]
  · simp only [lpnorm_eq_sum hp, Pi.conj_apply, IsROrC.norm_conj]

@[simp]
theorem lpnorm_conjneg [IsROrC β] (f : α → β) : ‖conjneg f‖_[p] = ‖f‖_[p] :=
  by
  simp only [conjneg, lpnorm_conj]
  cases p
  · simp only [Linftynorm_eq_csupr, ENNReal.none_eq_top, conjneg, IsROrC.norm_conj]
    exact (Equiv.neg _).iSup_congr fun _ => rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [L0norm_eq_card, Ne.def, ENNReal.some_eq_coe, ENNReal.coe_zero, Nat.cast_inj]
    exact
      card_congr (fun x _ => -x) (fun x hx => by simpa using hx) (fun x y _ _ => neg_inj.1)
        fun x hx => ⟨-x, by simpa using hx⟩
  · simp only [lpnorm_eq_sum hp, ENNReal.some_eq_coe]
    congr 1
    exact Fintype.sum_equiv (Equiv.neg _) _ _ fun _ => rfl

end lpnorm

section IsROrC

variable {α β : Type _} [Fintype α]

theorem L1norm_hMul [IsROrC β] (f g : α → β) : ‖f * g‖_[1] = ⟪fun i => ‖f i‖, fun i => ‖g i‖⟫_[ℝ] :=
  by simp [l2inner_eq_sum, L1norm_eq_sum]

end IsROrC

section wLpnorm

variable {α β : Type _} [AddCommGroup α] [Fintype α] {p : ℝ≥0} {w : α → ℝ≥0}

@[simp]
theorem wLpnorm_translate [NormedAddCommGroup β] (a : α) (f : α → β) :
    ‖τ a f‖_[p, τ a w] = ‖f‖_[p, w] :=
  (lpnorm_translate a fun i => w i ^ (p⁻¹ : ℝ) • ‖f i‖ : _)

@[simp]
theorem wLpnorm_conj [IsROrC β] (f : α → β) : ‖conj f‖_[p, w] = ‖f‖_[p, w] := by simp [wLpnorm]

@[simp]
theorem wLpnorm_conjneg [IsROrC β] (f : α → β) : ‖conjneg f‖_[p] = ‖f‖_[p] := by simp [wLpnorm]

end wLpnorm

/-- **Cauchy-Schwarz inequality** -/
theorem l2inner_le_L2norm_hMul_L2norm (f g : ι → ℝ) : ⟪f, g⟫_[ℝ] ≤ ‖f‖_[2] * ‖g‖_[2] :=
  real_inner_le_norm ((PiLp.equiv 2 _).symm f) _

namespace Tactic

open Positivity

/- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:87:10: unsupported modifiers in user command -/
alias ⟨_, Lpnorm_pos_of_ne_zero⟩ := lpnorm_pos

theorem lpnorm_pos_of_ne_zero' {α : Type _} [NormedAddCommGroup α] {p : ℝ≥0∞} {f : ι → α}
    (hf : f ≠ 0) : 0 < ‖f‖_[p] :=
  lpnorm_pos_of_ne_zero hf

theorem lpnorm_pos_of_pos {α : ι → Type _} [∀ i, NormedAddCommGroup (α i)] [∀ i, Preorder (α i)]
    {p : ℝ≥0∞} {f : ∀ i, α i} (hf : 0 < f) : 0 < ‖f‖_[p] :=
  lpnorm_pos_of_ne_zero hf.ne'

theorem lpnorm_pos_of_pos' {α : Type _} [NormedAddCommGroup α] [Preorder α] {p : ℝ≥0∞} {f : ι → α}
    (hf : 0 < f) : 0 < ‖f‖_[p] :=
  lpnorm_pos_of_ne_zero hf.ne'

section OrderedCommSemiring

variable [OrderedCommSemiring 𝕜] [StarOrderedRing 𝕜] {f g : ι → 𝕜}

private theorem L2inner_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[𝕜] :=
  l2inner_nonneg hf.le hg

private theorem L2inner_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫_[𝕜] :=
  l2inner_nonneg hf hg.le

private theorem L2inner_nonneg_of_pos_of_pos (hf : 0 < f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫_[𝕜] :=
  l2inner_nonneg hf.le hg.le

end OrderedCommSemiring

/-- Extension for the `positivity` tactic: Lp norms are nonnegative, and is strictly positive if its
input is nonzero. -/
@[positivity]
unsafe def positivity_Lpnorm : expr → tactic strictness
  | q(@lpnorm $(ι) $(hι) $(α) $(hα) $(p) $(f)) => do
    (-- if can prove `0 < a` or `a ≠ 0`, report positivity
        do
          let strict_f ← core f
          match strict_f with
            | positive hp =>
              positive <$> mk_mapp `` Lpnorm_pos_of_pos [ι, hι, α, hα, p, f, hp] <|>
                positive <$> mk_mapp `` Lpnorm_pos_of_pos' [ι, hι, none, none, none, p, f, hp]
            | nonzero hp =>
              positive <$> mk_mapp `` Lpnorm_pos_of_ne_zero [ι, hι, α, hα, p, f, hp] <|>
                positive <$> mk_mapp `` Lpnorm_pos_of_ne_zero' [ι, hι, none, none, p, f, hp]
            | _ => failed) <|>-- else report nonnegativity
          nonnegative <$>
          mk_mapp `` lpnorm_nonneg [none, none, none, none, p, f]
  | e => pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `‖f‖_[p]`"

/-- Extension for the `positivity` tactic: Lp norms are nonnegative, and is strictly positive if its
input is nonzero. -/
@[positivity]
unsafe def positivity_wLpnorm : expr → tactic strictness
  | q(‖$(f)‖_[$(p), $(w)]) =>
    nonnegative <$> mk_mapp `` wLpnorm_nonneg [none, none, none, none, p, w, f]
  | e => pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `‖f‖_[p, w]`"

/-- Extension for the `positivity` tactic: The inner product of nonnegative functions is
nonnegative. -/
@[positivity]
unsafe def positivity_L2inner : expr → tactic strictness
  | q(⟪$(f), $(g)⟫_[$(𝕜)]) => do
    let strict_f ← core f
    let strict_g ← core g
    match strict_f, strict_g with
      | positive hf, positive hg => nonnegative <$> mk_app `` L2inner_nonneg_of_pos_of_pos [hf, hg]
      | positive hf, nonnegative hg =>
        nonnegative <$> mk_app `` L2inner_nonneg_of_pos_of_nonneg [hf, hg]
      | nonnegative hf, positive hg =>
        nonnegative <$> mk_app `` L2inner_nonneg_of_nonneg_of_pos [hf, hg]
      | nonnegative hf, nonnegative hg => nonnegative <$> mk_app `` l2inner_nonneg [hf, hg]
      | _, _ => failed
  | e => pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `⟪f, g⟫_[𝕜]`"

end Tactic

section Examples

section NormedAddCommGroup

variable {α : ι → Type _} [∀ i, NormedAddCommGroup (α i)] {w : ι → ℝ≥0} {f : ∀ i, α i}

example {p : ℝ≥0∞} : 0 ≤ ‖f‖_[p] := by positivity

example {p : ℝ≥0∞} (hf : f ≠ 0) : 0 < ‖f‖_[p] := by positivity

example {p : ℝ≥0∞} {f : ι → ℝ} (hf : 0 < f) : 0 < ‖f‖_[p] := by positivity

example {p : ℝ≥0} : 0 ≤ ‖f‖_[p, w] := by positivity

end NormedAddCommGroup

section OrderedCommSemiring

variable [OrderedCommSemiring 𝕜] [StarOrderedRing 𝕜] {f g : ι → 𝕜}

example (hf : 0 < f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫_[𝕜] := by positivity

example (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[𝕜] := by positivity

example (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫_[𝕜] := by positivity

example (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[𝕜] := by positivity

end OrderedCommSemiring

section Complex

variable {w : ι → ℝ≥0} {f : ι → ℂ}

example {p : ℝ≥0∞} : 0 ≤ ‖f‖_[p] := by positivity

example {p : ℝ≥0∞} (hf : f ≠ 0) : 0 < ‖f‖_[p] := by positivity

example {p : ℝ≥0∞} {f : ι → ℝ} (hf : 0 < f) : 0 < ‖f‖_[p] := by positivity

example {p : ℝ≥0} : 0 ≤ ‖f‖_[p, w] := by positivity

end Complex

end Examples

/-! ### Hölder inequality -/


section lpnorm

variable {α : Type _} [Fintype α] {p q : ℝ≥0} {f g : α → ℝ}

@[simp]
theorem lpnorm_abs (p : ℝ≥0∞) (f : α → ℝ) : ‖|f|‖_[p] = ‖f‖_[p] := by simpa using lpnorm_norm p f

theorem L1norm_hMul_of_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f * g‖_[1] = ⟪f, g⟫_[ℝ] := by
  convert L1norm_hMul f g <;> ext a <;> refine' (norm_of_nonneg <| _).symm; exacts [hf _, hg _]

theorem lpnorm_rpow (hp : p ≠ 0) (hq : q ≠ 0) (hf : 0 ≤ f) :
    ‖f ^ (q : ℝ)‖_[p] = ‖f‖_[p * q] ^ (q : ℝ) :=
  by
  refine' rpow_left_inj_on (NNReal.coe_ne_zero.2 hp) lpnorm_nonneg (by dsimp <;> positivity) _
  dsimp
  rw [← rpow_mul lpnorm_nonneg, ← mul_comm, ← ENNReal.coe_mul, ← NNReal.coe_mul,
    lpnorm_rpow_eq_sum hp, lpnorm_rpow_eq_sum (mul_ne_zero hq hp)]
  simp [abs_rpow_of_nonneg (hf _), ← rpow_mul]

theorem L1norm_rpow (hq : q ≠ 0) (hf : 0 ≤ f) : ‖f ^ (q : ℝ)‖_[1] = ‖f‖_[q] ^ (q : ℝ) := by
  simpa only [ENNReal.coe_one, one_mul] using lpnorm_rpow one_ne_zero hq hf

theorem lpnorm_eq_L1norm_rpow (hp : p ≠ 0) (f : α → ℝ) :
    ‖f‖_[p] = ‖|f| ^ (p : ℝ)‖_[1] ^ (p⁻¹ : ℝ) := by
  simp [lpnorm_eq_sum hp, L1norm_eq_sum, abs_rpow_of_nonneg]

theorem lpnorm_rpow' (hp : p ≠ 0) (hq : q ≠ 0) (f : α → ℝ) :
    ‖f‖_[p] ^ (q : ℝ) = ‖|f| ^ (q : ℝ)‖_[p / q] := by
  rw [← ENNReal.coe_div hq,
    lpnorm_rpow (div_ne_zero hp hq) hq (LatticeOrderedCommGroup.abs_nonneg f), lpnorm_abs, ←
    ENNReal.coe_mul, div_mul_cancel _ hq]

--TODO: Generalise the following four to include `f g : α → ℂ`
/-- Hölder's inequality, binary case. -/
theorem l2inner_le_lpnorm_hMul_lpnorm (hpq : IsConjugateExponent p q) (f g : α → ℝ) :
    ⟪f, g⟫_[ℝ] ≤ ‖f‖_[p] * ‖g‖_[q] := by
  have hp := hpq.ne_zero
  have hq := hpq.symm.ne_zero
  norm_cast at hp hq 
  simpa [l2inner_eq_sum, lpnorm_eq_sum, *] using inner_le_Lp_mul_Lq _ f g hpq

/-- Hölder's inequality, binary case. -/
theorem abs_l2inner_le_lpnorm_hMul_lpnorm (hpq : IsConjugateExponent p q) (f g : α → ℝ) :
    |⟪f, g⟫_[ℝ]| ≤ ‖f‖_[p] * ‖g‖_[q] :=
  abs_l2inner_le_l2inner_abs.trans <|
    (l2inner_le_lpnorm_hMul_lpnorm hpq _ _).trans_eq <| by simp_rw [lpnorm_abs]

/-- Hölder's inequality, binary case. -/
theorem lpnorm_hMul_le (hp : p ≠ 0) (hq : q ≠ 0) (r : ℝ≥0) (hpqr : p⁻¹ + q⁻¹ = r⁻¹) (f g : α → ℝ) :
    ‖f * g‖_[r] ≤ ‖f‖_[p] * ‖g‖_[q] :=
  by
  have hr : r ≠ 0 := by
    rintro rfl
    simpa [hp] using hpqr
  have : |f * g| ^ (r : ℝ) = |f| ^ (r : ℝ) * |g| ^ (r : ℝ) := by ext <;> simp [mul_rpow, abs_mul]
  rw [lpnorm_eq_L1norm_rpow, rpow_inv_le_iff_of_pos, this, L1norm_hMul_of_nonneg,
    mul_rpow lpnorm_nonneg lpnorm_nonneg, lpnorm_rpow', lpnorm_rpow', ← ENNReal.coe_div, ←
    ENNReal.coe_div]
  refine' l2inner_le_lpnorm_hMul_lpnorm ⟨_, _⟩ _ _
  · norm_cast
    rw [div_eq_mul_inv, ← hpqr, mul_add, mul_inv_cancel hp]
    exact lt_add_of_pos_right _ (by positivity)
  · norm_cast
    simp [div_eq_mul_inv, hpqr, ← mul_add, hr]
  any_goals intro a; dsimp
  all_goals positivity

/-- Hölder's inequality, finitary case. -/
theorem lpnorm_prod_le {s : Finset ι} (hs : s.Nonempty) {p : ι → ℝ≥0} (hp : ∀ i, p i ≠ 0) (q : ℝ≥0)
    (hpq : ∑ i in s, (p i)⁻¹ = q⁻¹) (f : ι → α → ℝ) : ‖∏ i in s, f i‖_[q] ≤ ∏ i in s, ‖f i‖_[p i] :=
  by
  induction' s using Finset.cons_induction with i s hi ih generalizing q
  · cases not_nonempty_empty hs
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp only [sum_cons, sum_empty, add_zero, inv_inj] at hpq 
    simp [← hpq]
  simp_rw [prod_cons]
  rw [sum_cons, ← inv_inv (∑ _ in _, _ : ℝ≥0)] at hpq 
  refine'
    (lpnorm_hMul_le (hp _) (inv_ne_zero (sum_pos (fun _ _ => _) hs).ne') _ hpq _ _).trans
      (mul_le_mul_of_nonneg_left (ih hs _ (inv_inv _).symm) lpnorm_nonneg)
  exact pos_iff_ne_zero.2 (inv_ne_zero <| hp _)

end lpnorm

/-! ### Indicator -/


section indicate

variable {α β : Type _} [IsROrC β] [Fintype α] [DecidableEq α] {s : Finset α} {p : ℝ≥0}

theorem lpnorm_rpow_indicate (hp : p ≠ 0) (s : Finset α) : ‖𝟭_[β] s‖_[p] ^ (p : ℝ) = s.card :=
  by
  have : ∀ x, (ite (x ∈ s) 1 0 : ℝ) ^ (p : ℝ) = ite (x ∈ s) (1 ^ (p : ℝ)) (0 ^ (p : ℝ)) := fun x =>
    by split_ifs <;> simp
  simp [lpnorm_rpow_eq_sum, hp, indicate_apply, apply_ite Norm.norm, -sum_const, card_eq_sum_ones,
    sum_boole, this, zero_rpow, filter_mem_eq_inter]

theorem lpnorm_indicate (hp : p ≠ 0) (s : Finset α) : ‖𝟭_[β] s‖_[p] = s.card ^ (p⁻¹ : ℝ) := by
  refine' (eq_rpow_inv _ _ _).2 (lpnorm_rpow_indicate _ _) <;> positivity

theorem lpnorm_pow_indicate {p : ℕ} (hp : p ≠ 0) (s : Finset α) :
    ‖𝟭_[β] s‖_[p] ^ (p : ℝ) = s.card := by
  simpa using lpnorm_rpow_indicate (Nat.cast_ne_zero.2 hp) s

theorem L2norm_sq_indicate (s : Finset α) : ‖𝟭_[β] s‖_[2] ^ 2 = s.card := by
  simpa using lpnorm_pow_indicate two_ne_zero s

theorem L2norm_indicate (s : Finset α) : ‖𝟭_[β] s‖_[2] = Real.sqrt s.card := by
  rw [eq_comm, sqrt_eq_iff_sq_eq, L2norm_sq_indicate] <;> positivity

@[simp]
theorem L1norm_indicate (s : Finset α) : ‖𝟭_[β] s‖_[1] = s.card := by
  simpa using lpnorm_pow_indicate one_ne_zero s

end indicate

section mu

variable {α β : Type _} [IsROrC β] [Fintype α] [DecidableEq α] {s : Finset α} {p : ℝ≥0}

theorem lpnorm_mu (hp : 1 ≤ p) (hs : s.Nonempty) : ‖μ_[β] s‖_[p] = s.card ^ (p⁻¹ - 1 : ℝ) := by
  rw [mu, lpnorm_smul (ENNReal.one_le_coe_iff.2 hp) (s.card⁻¹ : β) (𝟭_[β] s), lpnorm_indicate,
      norm_inv, IsROrC.norm_natCast, inv_mul_eq_div, ← rpow_sub_one] <;>
    positivity

theorem lpnorm_mu_le (hp : 1 ≤ p) : ‖μ_[β] s‖_[p] ≤ s.card ^ (p⁻¹ - 1 : ℝ) :=
  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
    positivity
  · exact (lpnorm_mu hp hs).le

theorem L1norm_mu (hs : s.Nonempty) : ‖μ_[β] s‖_[1] = 1 := by simpa using lpnorm_mu le_rfl hs

theorem L1norm_mu_le_one : ‖μ_[β] s‖_[1] ≤ 1 := by simpa using lpnorm_mu_le le_rfl

end mu

