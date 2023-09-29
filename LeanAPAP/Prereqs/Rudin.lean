import LeanAPAP.Mathlib.Algebra.Support
import LeanAPAP.Mathlib.Analysis.Complex.Basic
import LeanAPAP.Mathlib.Data.Complex.Basic
import LeanAPAP.Mathlib.Data.Complex.Exponential
import LeanAPAP.Prereqs.Dissociation
import LeanAPAP.Prereqs.DFT

/-!
# Rudin's inequality
-/

open Finset Function Real
open Complex (I re im)
open scoped BigOps Nat NNReal ENNReal

variable {α : Type*} [Fintype α] [AddCommGroup α] {p : ℕ}

/-- **Rudin's inequality**, exponential form. -/
lemma rudin_exp_ineq (hp : 2 ≤ p) (f : α → ℂ) (hf : AddDissociated $ support $ dft f) :
    𝔼 a, exp |(f a).re| ≤ exp (‖f‖_[2] ^ 2 / 2) :=
  sorry

private lemma rudin_ineq_aux (hp : 2 ≤ p) (f : α → ℂ) (hf : AddDissociated $ support $ dft f) :
    ‖re ∘ f‖_[p] ≤ exp 2⁻¹ * sqrt p * ‖f‖_[2] := by
  wlog hfp : ‖f‖_[2] = sqrt p with H
  · obtain rfl | hf := eq_or_ne f 0
    · simp
    specialize H hp ((sqrt p / ‖f‖_[2]) • f) ?_
    · rwa [dft_smul, support_smul']
      sorry -- positivity
    simp_rw [Function.comp_def, Pi.smul_apply, Complex.smul_re, ←Pi.smul_def] at H
    rw [lpNorm_smul, lpNorm_smul, norm_div, norm_of_nonneg, norm_of_nonneg, div_mul_cancel,
      div_mul_comm, mul_le_mul_right, div_le_iff] at H
    exact H rfl
    · sorry -- positivity
    · positivity
    · sorry -- positivity
    · sorry -- positivity
    · positivity
    · norm_cast
      exact one_le_two.trans hp
    · norm_num
  have h := rudin_exp_ineq hp f hf
  rw [hfp, sq_sqrt] at h
  -- We currently can't fill the next `sorry`
  have : Fintype.card α * p ! ≤ p ^ p := sorry -- false because wrong normalisation
  replace h := (expect_le_expect λ a _ ↦ pow_div_factorial_le_exp sorry p).trans h
  simp_rw [←expect_div, expect, ←norm_eq_abs, card_univ, div_div, ←Nat.cast_mul] at h
  rw [←lpNorm_pow_eq_sum, div_le_iff, div_eq_inv_mul, exp_mul, rpow_nat_cast] at h
  replace h := h.trans $ mul_le_mul_of_nonneg_left (Nat.cast_le.2 this) $ by positivity
  rw [Nat.cast_pow, ←mul_pow, pow_le_pow_iff_left] at h
  rwa [hfp, mul_assoc, ←sq, sq_sqrt]
  all_goals sorry -- positivity

-- This actually uses `Complex.ext`

/-- **Rudin's inequality**, usual form. -/
lemma rudin_ineq (hp : 2 ≤ p) (f : α → ℂ) (hf : AddDissociated $ support $ dft f) :
    ‖f‖_[p] ≤ 2 * exp 2⁻¹ * sqrt p * ‖f‖_[2] := by
  have hp₁ : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast one_le_two.trans hp
  calc
    ‖f‖_[p] = ‖(fun a ↦ ((f a).re : ℂ)) + I • (fun a ↦ ((f a).im : ℂ))‖_[p]
      := by congr with a <;> simp
    _ ≤ ‖fun a ↦ ((f a).re : ℂ)‖_[p] + ‖I • (fun a ↦ ((f a).im : ℂ))‖_[p]
      := lpNorm_add_le hp₁ _ _
    _ = ‖re ∘ f‖_[p] + ‖re ∘ ((-I) • f)‖_[p] := by
        rw [lpNorm_smul hp₁, Complex.norm_I, one_mul, ←Complex.lpNorm_coe_comp,
          ←Complex.lpNorm_coe_comp]
        congr
        ext a : 1
        simp
    _ ≤ exp 2⁻¹ * sqrt p * ‖f‖_[2] + exp 2⁻¹ * sqrt p * ‖(-I) • f‖_[2]
      := add_le_add (rudin_ineq_aux hp _ hf) $ rudin_ineq_aux hp _ $ by
        rwa [dft_smul, support_smul']; simp
    _ = 2 * exp 2⁻¹ * sqrt p * ‖f‖_[2]
      := by rw [mul_assoc (2 : ℝ), mul_assoc (2 : ℝ), two_mul, lpNorm_smul one_le_two,
          norm_neg, Complex.norm_I, one_mul]
