import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import LeanAPAP.Mathlib.Algebra.Function.Support
import LeanAPAP.Mathlib.Analysis.Complex.Basic
import LeanAPAP.Mathlib.Data.Complex.Basic
import LeanAPAP.Mathlib.Data.Nat.Factorial.Basic
import LeanAPAP.Mathlib.Order.BooleanAlgebra
import LeanAPAP.Prereqs.Discrete.DFT.Compact
import LeanAPAP.Prereqs.Discrete.LpNorm.Compact
import LeanAPAP.Prereqs.Dissociation

/-!
# Rudin's inequality
-/

attribute [-simp] Complex.norm_eq_abs

open Finset hiding card
open Fintype (card)
open Function Real
open Complex (I re im)
open scoped BigOps Nat NNReal ENNReal ComplexConjugate ComplexOrder

variable {α : Type*} [Fintype α] [AddCommGroup α] {p : ℕ}

/-- A function of dissociated support can be randomised. -/
lemma AddDissociated.randomisation (c : AddChar α ℂ → ℝ) (d : AddChar α ℂ → ℂ)
    (hcd : AddDissociated {ψ | d ψ ≠ 0}) : 𝔼 a, ∏ ψ, (c ψ + (d ψ * ψ a).re) = ∏ ψ, c ψ := by
  refine Complex.ofReal_injective ?_
  push_cast
  calc
    _ = ∑ t, (𝔼 a, ∏ ψ ∈ t, ((d ψ * ψ a) + conj (d ψ * ψ a)) / 2) * ∏ ψ ∈ tᶜ, (c ψ : ℂ) := by
        simp_rw [expect_mul, ← expect_sum_comm, ← Fintype.prod_add, add_comm,
          Complex.re_eq_add_conj]
    _ = (𝔼 a, ∏ ψ ∈ ∅, ((d ψ * ψ a) + conj (d ψ * ψ a)) / 2) * ∏ ψ ∈ ∅ᶜ, (c ψ : ℂ) :=
        Fintype.sum_eq_single ∅ fun t ht ↦ mul_eq_zero_of_left ?_ _
    _ = _ := by simp
  simp only [map_mul, prod_div_distrib, prod_add, prod_const, ← expect_div, expect_sum_comm,
    div_eq_zero_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, card_eq_zero, compl_eq_empty_iff,
    false_and, or_false]
  rw [← expect_div]
  simp only [map_mul, prod_div_distrib, prod_add, prod_const, ← expect_div, expect_sum_comm,
    div_eq_zero_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, card_eq_zero, compl_eq_empty_iff,
    false_and, or_false]
  refine sum_eq_zero fun u _ ↦ ?_
  calc
    𝔼 a, (∏ ψ ∈ u, d ψ * ψ a) * ∏ ψ ∈ t \ u, conj (d ψ) * conj (ψ a)
      = ((∏ ψ ∈ u, d ψ) * ∏ ψ ∈ t \ u, conj (d ψ)) * 𝔼 a, (∑ ψ ∈ u, ψ - ∑ ψ ∈ t \ u, ψ) a := by
        simp_rw [mul_expect, AddChar.sub_apply, AddChar.sum_apply, mul_mul_mul_comm,
          ← prod_mul_distrib, AddChar.map_neg_eq_conj]
    _ = 0 := ?_
  rw [mul_eq_zero, AddChar.expect_eq_zero_iff_ne_zero, sub_ne_zero, or_iff_not_imp_left, ← Ne.def,
    mul_ne_zero_iff, prod_ne_zero_iff, prod_ne_zero_iff]
  exact fun h ↦ hcd.ne h.1 (by simpa only [map_ne_zero] using h.2) (sdiff_ne_right.2 $ .inl ht).symm

/-- **Rudin's inequality**, exponential form. -/
lemma rudin_exp_ineq (f : α → ℂ) (hf : AddDissociated $ support $ cft f) :
    𝔼 a, exp (f a).re ≤ exp (‖f‖ₙ_[2] ^ 2 / 2) := by
  have (z : ℂ) : exp (re z) ≤ cosh ‖z‖ + re (z / ‖z‖) * sinh ‖z‖ :=
    calc
      _ = _ := by obtain rfl | hz := eq_or_ne z 0 <;> simp [norm_pos_iff.2, *]
      _ ≤ _ := exp_mul_le_cosh_add_mul_sinh (by simpa [abs_div] using z.abs_re_div_abs_le_one) _
  choose c hc hcf using fun ψ ↦ Complex.exists_norm_mul_eq_self (cft f ψ)
  have hc₀ (ψ) : c ψ ≠ 0 := fun h ↦ by simpa [h] using hc ψ
  have (a) :
    exp (f a).re ≤ ∏ ψ, (cosh ‖cft f ψ‖ + (c ψ * sinh ‖cft f ψ‖ * ψ a).re) :=
    calc
      _ = ∏ ψ, exp ((cft f ψ * ψ a).re) := by simp_rw [← exp_sum, ← Complex.re_sum, cft_inversion]
      _ ≤ _ := prod_le_prod (fun _ _ ↦ by positivity) fun _ _ ↦ this _
      _ = ∏ ψ, (cosh ‖cft f ψ‖ + (c ψ * (cft f ψ * ψ a)
            / (c ψ * ↑‖cft f ψ‖)).re * sinh ‖cft f ψ‖) := by
          simp_rw [norm_mul, AddChar.norm_apply, mul_one, mul_div_mul_left _ _ (hc₀ _)]
      _ = _ := by
          congr with ψ
          obtain hψ | hψ := eq_or_ne (cft f ψ) 0
          · simp [hψ]
          · simp only [hcf, mul_left_comm (c _), mul_div_cancel_left _ hψ, ← Complex.re_mul_ofReal,
              mul_right_comm]
  calc
    _ ≤ 𝔼 a, ∏ ψ, (cosh ‖cft f ψ‖ + (c ψ * sinh ‖cft f ψ‖ * ψ a).re) :=
        expect_le_expect fun _ _ ↦ this _
    _ = ∏ ψ, cosh ‖cft f ψ‖ :=
        AddDissociated.randomisation _ _ $ by simpa [-Complex.ofReal_sinh, hc₀]
    _ ≤ ∏ ψ, exp (‖cft f ψ‖ ^ 2 / 2) :=
        prod_le_prod (fun _ _ ↦ by positivity) fun _ _ ↦ cosh_le_exp_half_sq _
    _ = _ := by simp_rw [← exp_sum, ← sum_div, ← l2Norm_cft, l2Norm_sq_eq_sum]

/-- **Rudin's inequality**, exponential form with absolute values. -/
lemma rudin_exp_abs_ineq (f : α → ℂ) (hf : AddDissociated $ support $ cft f) :
    𝔼 a, exp |(f a).re| ≤ 2 * exp (‖f‖ₙ_[2] ^ 2 / 2) := by
  calc
    _ ≤ 𝔼 a, (exp (f a).re + exp (-f a).re) := expect_le_expect fun _ _ ↦ exp_abs_le _
    _ = 𝔼 a, exp (f a).re + 𝔼 a, exp ((-f) a).re := by simp [expect_add_distrib]
    _ ≤ exp (‖f‖ₙ_[2] ^ 2 / 2) + exp (‖-f‖ₙ_[2] ^ 2 / 2) :=
        add_le_add (rudin_exp_ineq f hf) (rudin_exp_ineq (-f) $ by simpa using hf)
    _ = _ := by simp [two_mul]

private lemma rudin_ineq_aux (hp : 2 ≤ p) (f : α → ℂ) (hf : AddDissociated $ support $ cft f) :
    ‖re ∘ f‖ₙ_[p] ≤ 2 * exp 2⁻¹ * sqrt p * ‖f‖ₙ_[2] := by
  wlog hfp : ‖f‖ₙ_[2] = sqrt p with H
  · obtain rfl | hf := eq_or_ne f 0
    · simp
    specialize H hp ((sqrt p / ‖f‖ₙ_[2]) • f) ?_
    · rwa [cft_smul, support_smul']
      positivity
    simp_rw [Function.comp_def, Pi.smul_apply, Complex.smul_re, ←Pi.smul_def] at H
    rw [nlpNorm_smul, nlpNorm_smul, norm_div, norm_of_nonneg, norm_of_nonneg, mul_left_comm,
      mul_le_mul_left] at H
    refine H ?_
    rw [div_mul_cancel]
    any_goals positivity
    · norm_cast
      exact one_le_two.trans hp
    · norm_num
  have hp₀ : p ≠ 0 := by positivity
  have : (‖re ∘ f‖ₙ_[↑p] / p) ^ p ≤ (2 * exp 2⁻¹) ^ p := by
    calc
      _ = 𝔼 a, |(f a).re| ^ p / p ^ p := by
          simp [div_pow, nlpNorm_pow_eq_expect hp₀]; rw [expect_div]
      _ ≤ 𝔼 a, |(f a).re| ^ p / p ! := by gcongr; norm_cast; exact p.factorial_le_pow
      _ ≤ 𝔼 a, exp |(f a).re| := by gcongr; exact pow_div_factorial_le_exp _ (abs_nonneg _) _
      _ ≤ _ := rudin_exp_abs_ineq f hf
      _ ≤ 2 ^ p * exp (‖f‖ₙ_[2] ^ 2 / 2) := by gcongr; exact le_self_pow one_le_two hp₀
      _ = (2 * exp 2⁻¹) ^ p := by
          rw [hfp, sq_sqrt, mul_pow, ← exp_nsmul, nsmul_eq_mul, div_eq_mul_inv]; positivity
  refine le_of_pow_le_pow_left hp₀ (by positivity) ?_
  rwa [hfp, mul_assoc, mul_self_sqrt, mul_pow, ← div_le_iff, ← div_pow]
  all_goals positivity

/-- **Rudin's inequality**, usual form. -/
lemma rudin_ineq (hp : 2 ≤ p) (f : α → ℂ) (hf : AddDissociated $ support $ cft f) :
    ‖f‖ₙ_[p] ≤ 4 * exp 2⁻¹ * sqrt p * ‖f‖ₙ_[2] := by
  have hp₁ : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast one_le_two.trans hp
  calc
    ‖f‖ₙ_[p] = ‖(fun a ↦ ((f a).re : ℂ)) + I • (fun a ↦ ((f a).im : ℂ))‖ₙ_[p]
      := by congr with a; simp [mul_comm I]
    _ ≤ ‖fun a ↦ ((f a).re : ℂ)‖ₙ_[p] + ‖I • (fun a ↦ ((f a).im : ℂ))‖ₙ_[p]
      := nlpNorm_add_le hp₁ _ _
    _ = ‖re ∘ f‖ₙ_[p] + ‖re ∘ ((-I) • f)‖ₙ_[p] := by
        rw [nlpNorm_smul hp₁, Complex.norm_I, one_mul, ←Complex.nlpNorm_coe_comp,
          ←Complex.nlpNorm_coe_comp]
        congr
        ext a : 1
        simp
    _ ≤ 2 * exp 2⁻¹ * sqrt p * ‖f‖ₙ_[2] + 2 * exp 2⁻¹ * sqrt p * ‖(-I) • f‖ₙ_[2]
      := add_le_add (rudin_ineq_aux hp _ hf) $ rudin_ineq_aux hp _ $ by
        rwa [cft_smul, support_smul']; simp
    _ = 4 * exp 2⁻¹ * sqrt p * ‖f‖ₙ_[2] := by
        rw [nlpNorm_smul one_le_two, norm_neg, Complex.norm_I, one_mul]; ring
