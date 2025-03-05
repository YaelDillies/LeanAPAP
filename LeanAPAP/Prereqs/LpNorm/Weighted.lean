import Mathlib.Algebra.Group.Translate
import Mathlib.Algebra.Star.Conjneg
import LeanAPAP.Prereqs.LpNorm.Discrete.Defs

/-!
# Lp norms
-/

open Finset Function Real MeasureTheory
open scoped ComplexConjugate ENNReal NNReal translate

variable {α 𝕜 E : Type*} [MeasurableSpace α]

/-! #### Weighted Lp norm -/

section NormedAddCommGroup
variable [NormedAddCommGroup E] {p q : ℝ≥0∞} {w : α → ℝ≥0} {f g h : α → E}

/-- The weighted Lp norm of a function. -/
noncomputable def wLpNorm (p : ℝ≥0∞) (w : α → ℝ≥0) (f : α → E) : ℝ≥0 :=
  nnLpNorm f p <| .sum fun i ↦ w i • .dirac i

notation "‖" f "‖_[" p ", " w "]" => wLpNorm p w f

@[simp] lemma wLpNorm_zero (w : α → ℝ≥0) : ‖(0 : α → E)‖_[p, w] = 0 := by simp [wLpNorm]

@[simp] lemma wLpNorm_neg (w : α → ℝ≥0) (f : α → E) : ‖-f‖_[p, w] = ‖f‖_[p, w] := by
  simp [wLpNorm]

lemma wLpNorm_sub_comm (w : α → ℝ≥0) (f g : α → E) : ‖f - g‖_[p, w] = ‖g - f‖_[p, w] := by
  simp [wLpNorm, nnLpNorm_sub_comm]

@[simp] lemma wLpNorm_one_eq_dLpNorm (p : ℝ≥0∞) (f : α → E) : ‖f‖_[p, 1] = ‖f‖_[p] := by
  simp [wLpNorm, dLpNorm, nnLpNorm, Measure.count]

@[simp] lemma wLpNorm_exponent_zero (w : α → ℝ≥0) (f : α → E) : ‖f‖_[0, w] = 0 := by simp [wLpNorm]

@[simp] lemma wLpNorm_norm (w : α → ℝ≥0) (f : α → E) : ‖fun i ↦ ‖f i‖‖_[p, w] = ‖f‖_[p, w] := by
  simp [wLpNorm]

lemma wLpNorm_smul [NormedField 𝕜] [NormedSpace 𝕜 E] (c : 𝕜) (f : α → E) (p : ℝ≥0∞) (w : α → ℝ≥0) :
    ‖c • f‖_[p, w] = ‖c‖₊ * ‖f‖_[p, w] := nnLpNorm_const_smul ..

lemma wLpNorm_nsmul [NormedSpace ℝ E] (n : ℕ) (f : α → E) (p : ℝ≥0∞) (w : α → ℝ≥0) :
    ‖n • f‖_[p, w] = n • ‖f‖_[p, w] := nnLpNorm_nsmul ..

section RCLike
variable {K : Type*} [RCLike K]

@[simp] lemma wLpNorm_conj (f : α → K) : ‖conj f‖_[p, w] = ‖f‖_[p, w] := by simp [← wLpNorm_norm]

end RCLike

variable [Fintype α]

@[simp] lemma wLpNorm_const_right (hp : p ≠ ∞) (w : ℝ≥0) (f : α → E) :
    ‖f‖_[p, const _ w] = w ^ p.toReal⁻¹ * ‖f‖_[p] := by
  simp [wLpNorm, dLpNorm, ← Finset.smul_sum, nnLpNorm_smul_measure_of_ne_top hp, Measure.count]

@[simp] lemma wLpNorm_smul_right (hp : p ≠ ⊤) (c : ℝ≥0) (f : α → E) :
    ‖f‖_[p, c • w] = c ^ p.toReal⁻¹ * ‖f‖_[p, w] := by
  simp [wLpNorm, mul_smul, ← Finset.smul_sum, nnLpNorm_smul_measure_of_ne_top hp]

variable [DiscreteMeasurableSpace α]

lemma wLpNorm_eq_sum_norm (hp₀ : p ≠ 0) (hp : p ≠ ∞) (w : α → ℝ≥0) (f : α → E) :
    ‖f‖_[p, w] = (∑ i, w i • ‖f i‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  simp [wLpNorm, coe_nnLpNorm_eq_integral_norm_rpow_toReal hp₀ hp .of_discrete, one_div,
    integral_finset_sum_measure, tsum_eq_sum' (s := univ) (by simp), ENNReal.coe_rpow_of_nonneg,
    ENNReal.toReal_inv, NNReal.smul_def]

lemma wLpNorm_eq_sum_nnnorm (hp₀ : p ≠ 0) (hp : p ≠ ∞) (w : α → ℝ≥0) (f : α → E) :
    ‖f‖_[p, w] = (∑ i, w i • ‖f i‖₊ ^ p.toReal) ^ p.toReal⁻¹ := by
  ext; simpa using wLpNorm_eq_sum_norm hp₀ hp ..

lemma wLpNorm_toNNReal_eq_sum_norm {p : ℝ} (hp : 0 < p) (w : α → ℝ≥0) (f : α → E) :
    ‖f‖_[p.toNNReal, w] = (∑ i, w i • ‖f i‖ ^ p) ^ p⁻¹ := by
  rw [wLpNorm_eq_sum_norm] <;> simp [hp, hp.ne', hp.le, NNReal.smul_def]

lemma wLpNorm_toNNReal_eq_sum {p : ℝ} (hp : 0 < p) (w : α → ℝ≥0) (f : α → E) :
    ‖f‖_[p.toNNReal, w] = (∑ i, w i • ‖f i‖₊ ^ p) ^ p⁻¹ := by
  rw [wLpNorm_eq_sum_nnnorm] <;> simp [hp, hp.ne', hp.le, NNReal.smul_def]

lemma wLpNorm_rpow_eq_sum_nnnorm {p : ℝ≥0} (hp : p ≠ 0) (w : α → ℝ≥0) (f : α → E) :
    ‖f‖_[p, w] ^ (p : ℝ) = ∑ i, w i • ‖f i‖₊ ^ (p : ℝ) := by simp [wLpNorm_eq_sum_nnnorm, hp]

lemma wLpNorm_rpow_eq_sum_norm {p : ℝ≥0} (hp : p ≠ 0) (w : α → ℝ≥0) (f : α → E) :
    ‖f‖_[p, w] ^ (p : ℝ) = ∑ i, w i • ‖f i‖ ^ (p : ℝ) := by
  simpa using NNReal.coe_inj.2 (wLpNorm_rpow_eq_sum_nnnorm hp ..)

lemma wLpNorm_pow_eq_sum_nnnorm {p : ℕ} (hp : p ≠ 0) (w : α → ℝ≥0) (f : α → E) :
    ‖f‖_[p, w] ^ p = ∑ i, w i • ‖f i‖₊ ^ p := by
  simpa using wLpNorm_rpow_eq_sum_nnnorm (Nat.cast_ne_zero.2 hp) w f

lemma wLpNorm_pow_eq_sum_norm {p : ℕ} (hp : p ≠ 0) (w : α → ℝ≥0) (f : α → E) :
    ‖f‖_[p, w] ^ p = ∑ i, w i • ‖f i‖ ^ p := by
  simpa using wLpNorm_rpow_eq_sum_norm (Nat.cast_ne_zero.2 hp) w f

lemma wL1Norm_eq_sum_nnnorm (w : α → ℝ≥0) (f : α → E) : ‖f‖_[1, w] = ∑ i, w i • ‖f i‖₊ := by
  simp [wLpNorm_eq_sum_nnnorm]

lemma wL1Norm_eq_sum_norm (w : α → ℝ≥0) (f : α → E) : ‖f‖_[1, w] = ∑ i, w i • ‖f i‖ := by
  simp [wLpNorm_eq_sum_norm]

@[gcongr]
lemma wLpNorm_mono_right (hpq : p ≤ q) (w : α → ℝ≥0) (f : α → E) : ‖f‖_[p, w] ≤ ‖f‖_[q, w] :=
  sorry

section one_le

lemma wLpNorm_add_le (hp : 1 ≤ p) (w : α → ℝ≥0) (f g : α → E) :
    ‖f + g‖_[p, w] ≤ ‖f‖_[p, w] + ‖g‖_[p, w] := nnLpNorm_add_le .of_discrete .of_discrete hp

lemma wLpNorm_sub_le (hp : 1 ≤ p) (w : α → ℝ≥0) (f g : α → E) :
    ‖f - g‖_[p, w] ≤ ‖f‖_[p, w] + ‖g‖_[p, w] := by
  simpa [sub_eq_add_neg] using wLpNorm_add_le hp w f (-g)

lemma wLpNorm_le_wLpNorm_add_wLpNorm_sub' (hp : 1 ≤ p) (w : α → ℝ≥0) (f g : α → E) :
    ‖f‖_[p, w] ≤ ‖g‖_[p, w] + ‖f - g‖_[p, w] := by simpa using wLpNorm_add_le hp w g (f - g)

lemma wLpNorm_le_wLpNorm_add_wLpNorm_sub (hp : 1 ≤ p) (w : α → ℝ≥0) (f g : α → E) :
    ‖f‖_[p, w] ≤ ‖g‖_[p, w] + ‖g - f‖_[p, w] := by
  rw [wLpNorm_sub_comm]; exact wLpNorm_le_wLpNorm_add_wLpNorm_sub' hp ..

lemma wLpNorm_le_add_wLpNorm_add (hp : 1 ≤ p) (w : α → ℝ≥0) (f g : α → E) :
    ‖f‖_[p, w] ≤ ‖f + g‖_[p, w] + ‖g‖_[p, w] := by simpa using wLpNorm_add_le hp w (f + g) (-g)

lemma wLpNorm_sub_le_wLpNorm_sub_add_wLpNorm_sub (hp : 1 ≤ p) (f g : α → E) :
    ‖f - h‖_[p, w] ≤ ‖f - g‖_[p, w] + ‖g - h‖_[p, w] := by
  simpa using wLpNorm_add_le hp w (f - g) (g - h)

end one_le

end NormedAddCommGroup

section Real
variable [Fintype α] [DiscreteMeasurableSpace α] {p : ℝ≥0∞} {w : α → ℝ≥0} {f g : α → ℝ}

@[simp]
lemma wLpNorm_one (hp₀ : p ≠ 0) (hp : p ≠ ∞) (w : α → ℝ≥0) :
    ‖(1 : α → ℝ)‖_[p, w] = (∑ i, w i) ^ p.toReal⁻¹ := by simp [wLpNorm_eq_sum_nnnorm hp₀ hp]

lemma wLpNorm_mono (hf : 0 ≤ f) (hfg : f ≤ g) : ‖f‖_[p, w] ≤ ‖g‖_[p, w] :=
  nnLpNorm_mono_real .of_discrete (by simpa [abs_of_nonneg (hf _)])

end Real

section wLpNorm
variable [Fintype α] [DiscreteMeasurableSpace α] {p : ℝ≥0} {w : α → ℝ≥0}

variable [AddCommGroup α]

@[simp] lemma wLpNorm_translate [NormedAddCommGroup E] (a : α) (f : α → E) :
    ‖τ a f‖_[p, τ a w] = ‖f‖_[p, w] := by
  obtain rfl | hp := eq_or_ne p 0 <;>
    simp [wLpNorm_eq_sum_nnnorm, *, ← sum_translate a fun x ↦ w x * ‖f x‖₊ ^ (_ : ℝ)]

end wLpNorm
