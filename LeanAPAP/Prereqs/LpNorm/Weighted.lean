import LeanAPAP.Prereqs.LpNorm.Discrete.Basic

/-!
# Lp norms
-/

open Finset Function Real
open scoped ComplexConjugate ENNReal NNReal

variable {ι 𝕜 : Type*} [Fintype ι]

/-! #### Weighted Lp norm -/

section NormedAddCommGroup
variable {α : ι → Type*} [∀ i, NormedAddCommGroup (α i)] {p q : ℝ≥0} {w : ι → ℝ≥0}
  {f g h : ∀ i, α i}

/-- The weighted Lp norm of a function. -/
noncomputable def wlpNorm (p : ℝ≥0) (w : ι → ℝ≥0) (f : ∀ i, α i) : ℝ :=
  ‖fun i ↦ w i ^ (p⁻¹ : ℝ) • ‖f i‖‖_[p]

notation "‖" f "‖_[" p ", " w "]" => wlpNorm p w f

@[simp]
lemma wlpNorm_one_eq_lpNorm (p : ℝ≥0) (f : ∀ i, α i) : ‖f‖_[p, 1] = ‖f‖_[p] := by
  simp [wlpNorm, l0Norm_eq_zero, lpNorm_eq_sum, *]

@[simp]
lemma wlpNorm_const_right (hp : 1 ≤ p) (w : ℝ≥0) (f : ∀ i, α i) :
    ‖f‖_[p, const _ w] = w ^ (p⁻¹ : ℝ) * ‖f‖_[p] := by
  simpa [wlpNorm, -norm_eq_abs, norm_of_nonneg, Pi.smul_def, NNReal.smul_def, rpow_nonneg] using
    lpNorm_smul (ENNReal.one_le_coe_iff.2 hp) (w ^ (p⁻¹ : ℝ) : ℝ) fun i ↦ ‖f i‖

lemma wlpNorm_eq_sum (hp : p ≠ 0) (w : ι → ℝ≥0) (f : ∀ i, α i) :
    ‖f‖_[p, w] = (∑ i, w i • ‖f i‖ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) := by
  have : (p : ℝ) ≠ 0 := by positivity
  simp_rw [wlpNorm, lpNorm_eq_sum hp, NNReal.smul_def, norm_smul]
  simp only [NNReal.coe_rpow, norm_norm, Algebra.id.smul_eq_mul, mul_rpow, norm_nonneg,
    rpow_nonneg, hp, NNReal.coe_nonneg, norm_of_nonneg, rpow_inv_rpow _ this]

lemma wlpNorm_eq_sum' {p : ℝ} (hp : 0 < p) (w : ι → ℝ≥0) (f : ∀ i, α i) :
    ‖f‖_[p.toNNReal, w] = (∑ i, w i • ‖f i‖ ^ p) ^ p⁻¹ := by
  rw [wlpNorm_eq_sum] <;> simp [hp, hp.ne', hp.le]

lemma wlpNorm_rpow_eq_sum {p : ℝ≥0} (hp : p ≠ 0) (w : ι → ℝ≥0) (f : ∀ i, α i) :
    ‖f‖_[p, w] ^ (p : ℝ) = ∑ i, w i • ‖f i‖ ^ (p : ℝ) := by
  rw [wlpNorm_eq_sum hp, rpow_inv_rpow] -- positivity
  · exact sum_nonneg fun _ _ ↦ by positivity
  · positivity

lemma wlpNorm_pow_eq_sum {p : ℕ} (hp : p ≠ 0) (w : ι → ℝ≥0) (f : ∀ i, α i) :
    ‖f‖_[p, w] ^ p = ∑ i, w i • ‖f i‖ ^ p := by
  simpa using wlpNorm_rpow_eq_sum (Nat.cast_ne_zero.2 hp) w f

lemma wl1Norm_eq_sum (w : ι → ℝ≥0) (f : ∀ i, α i) : ‖f‖_[1, w] = ∑ i, w i • ‖f i‖ := by
  simp [wlpNorm_eq_sum]

lemma wl0Norm_eq_zero (w : ι → ℝ≥0) (f : ∀ i, α i) :
    ‖f‖_[0, w] = {i | f i ≠ 0}.toFinite.toFinset.card := by simp [wlpNorm, l0Norm_eq_zero]

@[simp]
lemma wlpNorm_zero (w : ι → ℝ≥0) : ‖(0 : ∀ i, α i)‖_[p, w] = 0 := by simp [wlpNorm, ←Pi.zero_def]

@[simp] lemma wlpNorm_norm (w : ι → ℝ≥0) (f : ∀ i, α i) : ‖fun i ↦ ‖f i‖‖_[p, w] = ‖f‖_[p, w] := by
  obtain rfl | hp := @eq_zero_or_pos _ _ p <;> simp [wl0Norm_eq_zero, wlpNorm_eq_sum, *, ne_of_gt]

@[simp]lemma wlpNorm_neg (w : ι → ℝ≥0) (f : ∀ i, α i) : ‖-f‖_[p, w] = ‖f‖_[p, w] := by
  simp [←wlpNorm_norm _ (-f)]

lemma wlpNorm_sub_comm (w : ι → ℝ≥0) (f g : ∀ i, α i) : ‖f - g‖_[p, w] = ‖g - f‖_[p, w] := by
  simp [←wlpNorm_neg _ (f - g)]

@[simp] lemma wlpNorm_nonneg : 0 ≤ ‖f‖_[p, w] := lpNorm_nonneg

lemma wlpNorm_mono_right (hpq : p ≤ q) (w : ι → ℝ≥0) (f : ∀ i, α i) : ‖f‖_[p, w] ≤ ‖f‖_[q, w] :=
  sorry

section one_le

lemma wlpNorm_add_le (hp : 1 ≤ p) (w : ι → ℝ≥0) (f g : ∀ i, α i) :
    ‖f + g‖_[p, w] ≤ ‖f‖_[p, w] + ‖g‖_[p, w] := by
  unfold wlpNorm
  refine (lpNorm_add_le (by exact_mod_cast hp) _ _).trans'
    (lpNorm_mono (fun i ↦ by dsimp; positivity) fun i ↦ ?_)
  dsimp
  rw [←smul_add]
  exact smul_le_smul_of_nonneg_left (norm_add_le _ _) (zero_le _)

lemma wlpNorm_sub_le (hp : 1 ≤ p) (w : ι → ℝ≥0) (f g : ∀ i, α i) :
    ‖f - g‖_[p, w] ≤ ‖f‖_[p, w] + ‖g‖_[p, w] := by
  simpa [sub_eq_add_neg] using wlpNorm_add_le hp w f (-g)

lemma wlpNorm_le_wlpNorm_add_wlpNorm_sub' (hp : 1 ≤ p) (w : ι → ℝ≥0) (f g : ∀ i, α i) :
    ‖f‖_[p, w] ≤ ‖g‖_[p, w] + ‖f - g‖_[p, w] := by simpa using wlpNorm_add_le hp w g (f - g)

lemma wlpNorm_le_wlpNorm_add_wlpNorm_sub (hp : 1 ≤ p) (w : ι → ℝ≥0) (f g : ∀ i, α i) :
    ‖f‖_[p, w] ≤ ‖g‖_[p, w] + ‖g - f‖_[p, w] := by
  rw [wlpNorm_sub_comm]; exact wlpNorm_le_wlpNorm_add_wlpNorm_sub' hp _ _ _

lemma wlpNorm_le_add_wlpNorm_add (hp : 1 ≤ p) (w : ι → ℝ≥0) (f g : ∀ i, α i) :
    ‖f‖_[p, w] ≤ ‖f + g‖_[p, w] + ‖g‖_[p, w] := by simpa using wlpNorm_add_le hp w (f + g) (-g)

lemma wlpNorm_sub_le_wlpNorm_sub_add_wlpNorm_sub (hp : 1 ≤ p) (f g : ∀ i, α i) :
    ‖f - h‖_[p, w] ≤ ‖f - g‖_[p, w] + ‖g - h‖_[p, w] := by
  simpa using wlpNorm_add_le hp w (f - g) (g - h)

variable [NormedField 𝕜] [∀ i, NormedSpace 𝕜 (α i)]

-- TODO: `p ≠ 0` is enough
lemma wlpNorm_smul (hp : 1 ≤ p) (c : 𝕜) (f : ∀ i, α i) : ‖c • f‖_[p, w] = ‖c‖ * ‖f‖_[p, w] := by
  rw [wlpNorm, wlpNorm]
  have : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  have := lpNorm_smul this ‖c‖ fun i ↦ w i ^ (p⁻¹ : ℝ) • ‖f i‖
  rw [norm_norm] at this
  rw [←this]
  congr with i : 1
  simp only [Pi.smul_apply, Algebra.id.smul_eq_mul, Algebra.mul_smul_comm, norm_smul]

@[simp]
lemma wlpNorm_smul_right (hp : p ≠ 0) (c : ℝ≥0) (f : ∀ i, α i) :
    ‖f‖_[p, c • w] = c ^ (p⁻¹ : ℝ) * ‖f‖_[p, w] := by
  simp only [wlpNorm_eq_sum hp, NNReal.smul_def, Pi.smul_apply, Algebra.id.smul_eq_mul,
    NNReal.coe_mul, mul_assoc, ←mul_sum]
  exact mul_rpow (by positivity) (sum_nonneg fun _ _ ↦ by positivity) -- positivity

variable [∀ i, NormedSpace ℝ (α i)]

lemma wlpNorm_nsmul (hp : 1 ≤ p) (n : ℕ) (w : ι → ℝ≥0) (f : ∀ i, α i) :
    ‖n • f‖_[p, w] = n • ‖f‖_[p, w] := by
  rw [← Nat.cast_smul_eq_nsmul ℝ, wlpNorm_smul hp, RCLike.norm_natCast, nsmul_eq_mul]

end one_le

end NormedAddCommGroup

section Real
variable {p : ℝ≥0} {w : ι → ℝ≥0} {f g : ι → ℝ}

@[simp]
lemma wlpNorm_one (hp : p ≠ 0) (w : ι → ℝ≥0) :
    ‖(1 : ι → ℝ)‖_[p, w] = (∑ i, w i : ℝ) ^ (p⁻¹ : ℝ) := by
  simp [wlpNorm_eq_sum hp, NNReal.smul_def]

lemma wlpNorm_mono (hf : 0 ≤ f) (hfg : f ≤ g) : ‖f‖_[p, w] ≤ ‖g‖_[p, w] :=
  lpNorm_mono (fun i ↦ by dsimp; positivity) fun i ↦ smul_le_smul_of_nonneg_left
    (by rw [norm_of_nonneg (hf _), norm_of_nonneg (hf.trans hfg _)]; exact hfg _) $ by positivity

end Real

section wlpNorm
variable {α β : Type*} [AddCommGroup α] [Fintype α] {p : ℝ≥0} {w : α → ℝ≥0}

@[simp] lemma wlpNorm_translate [NormedAddCommGroup β] (a : α) (f : α → β) :
    ‖τ a f‖_[p, τ a w] = ‖f‖_[p, w] :=
  (lpNorm_translate a fun i ↦ w i ^ (p⁻¹ : ℝ) • ‖f i‖ : _)

@[simp]
lemma wlpNorm_conj [RCLike β] (f : α → β) : ‖conj f‖_[p, w] = ‖f‖_[p, w] := by simp [wlpNorm]

@[simp]
lemma wlpNorm_conjneg [RCLike β] (f : α → β) : ‖conjneg f‖_[p] = ‖f‖_[p] := by simp [wlpNorm]

end wlpNorm

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

/-- The `positivity` extension which identifies expressions of the form `‖f‖_[p, w]`. -/
@[positivity ‖_‖_[_, _]] def evalWLpNorm : PositivityExt where eval {u α} _ _ e := do
  if let 0 := u then -- lean4#3060 means we can't combine this with the match below
    match α, e with
    | ~q(ℝ), ~q(@wlpNorm $ι $instι $α $instnorm $p $w $f) =>
          assumeInstancesCommute
          return .nonnegative q(wlpNorm_nonneg)
    | _ => throwError "not wlpNorm"
  else
    throwError "not wlpNorm"

section Examples
section NormedAddCommGroup
variable {α : ι → Type*} [∀ i, NormedAddCommGroup (α i)] {w : ι → ℝ≥0} {f : ∀ i, α i}

example {p : ℝ≥0} : 0 ≤ ‖f‖_[p, w] := by positivity

end NormedAddCommGroup

section Complex
variable {w : ι → ℝ≥0} {f : ι → ℂ}

example {p : ℝ≥0} : 0 ≤ ‖f‖_[p, w] := by positivity

end Complex
end Examples
end Mathlib.Meta.Positivity
