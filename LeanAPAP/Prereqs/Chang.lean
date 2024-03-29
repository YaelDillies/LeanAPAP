import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities
import LeanAPAP.Prereqs.Curlog
import LeanAPAP.Prereqs.Energy
import LeanAPAP.Prereqs.LargeSpec
import LeanAPAP.Prereqs.Rudin

/-!
# Chang's lemma
-/

open Finset Fintype Function Real
open scoped BigOperators ComplexConjugate ComplexOrder NNReal

variable {G : Type*} [AddCommGroup G] [Fintype G] {f : G → ℂ} {η : ℝ} {ψ : AddChar G ℂ}
  {Δ : Finset (AddChar G ℂ)} {m : ℕ}

private noncomputable def α (f : G → ℂ) := ‖f‖_[1] ^ 2 / ‖f‖_[2] ^ 2 / card G

lemma α_nonneg (f : G → ℂ) : 0 ≤ α f := by unfold α; positivity
lemma α_pos (hf : f ≠ 0) : 0 < α f := by unfold α; positivity

lemma α_le_one (f : G → ℂ) : α f ≤ 1 := by
  refine' div_le_one_of_le (div_le_of_nonneg_of_le_mul _ _ _) _
  any_goals positivity
  rw [l1Norm_eq_sum, l2Norm_sq_eq_sum]
  exact sq_sum_le_card_mul_sum_sq

lemma general_hoelder (hη : 0 ≤ η) (ν : G → ℝ≥0) (hfν : ∀ x, f x ≠ 0 → 1 ≤ ν x)
    (hΔ : Δ ⊆ largeSpec f η) (hm : m ≠ 0) :
    ↑Δ.card ^ (2 * m) * (η ^ (2 * m) * (‖f‖_[1] ^ 2 / ‖f‖_[2] ^ 2)) ≤
      energy m Δ (dft fun a ↦ ν a) := by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  choose c norm_c hc using fun γ ↦ RCLike.exists_norm_eq_mul_self (dft f γ)
  have :=
    calc
      η * ‖f‖_[1] * Δ.card ≤ ∑ γ in Δ, ‖dft f γ‖ := ?_
      _ ≤ ‖∑ x, f x * ∑ γ in Δ, c γ * conj (γ x)‖ := ?_
      _ ≤ ∑ x, ‖f x * ∑ γ in Δ, c γ * conj (γ x)‖ := (norm_sum_le _ _)
      _ = ∑ x, ‖f x‖ * ‖∑ γ in Δ, c γ * conj (γ x)‖ := by simp_rw [norm_mul]
      _ ≤ _ := inner_le_weight_mul_Lp_of_nonneg _ (p := m) ?_ _ _ (fun _ ↦ norm_nonneg _)
            fun _ ↦ norm_nonneg _
      _ = ‖f‖_[1] ^ (1 - (m : ℝ)⁻¹) * (∑ x, ‖f x‖ * ‖∑ γ in Δ, c γ * conj (γ x)‖ ^ m) ^ (m⁻¹ : ℝ) :=
        by push_cast; simp_rw [l1Norm_eq_sum, rpow_nat_cast]
  rotate_left
  · rw [←nsmul_eq_mul']
    exact card_nsmul_le_sum _ _ _ fun x hx ↦ mem_largeSpec.1 $ hΔ hx
  · simp_rw [mul_sum, mul_comm (f _), mul_assoc (c _), @sum_comm _ _ G, ←mul_sum, ←l2Inner_eq_sum,
      ←dft_apply, ←hc, ←RCLike.ofReal_sum, RCLike.norm_ofReal]
    exact le_abs_self _
  · norm_cast
    exact hm.bot_lt
  replace this := pow_le_pow_left (by positivity) this m
  simp_rw [mul_pow] at this
  rw [rpow_inv_natCast_pow _ hm, ←rpow_mul_natCast, one_sub_mul,
    inv_mul_cancel, ←Nat.cast_pred, rpow_nat_cast, mul_assoc, mul_left_comm, ←pow_sub_one_mul,
    mul_assoc, mul_le_mul_left] at this
  any_goals positivity
  replace hfν : ∀ x, ‖f x‖ ≤ ‖f x‖ * sqrt (ν x) := by
    rintro x
    obtain hfx | hfx := eq_or_ne (f x) 0
    · simp [hfx]
    · exact le_mul_of_one_le_right (norm_nonneg _) $ one_le_sqrt.2 $ NNReal.one_le_coe.2 $
        hfν _ hfx
  replace this :=
    calc
      _ ≤ (∑ x, ‖f x‖ * sqrt (ν x) * ‖∑ γ in Δ, c γ * conj (γ x)‖ ^ m) ^ 2 :=
          pow_le_pow_left (by positivity)
            (this.trans $ sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_right (hfν _) $ by positivity) _
      _ = (∑ x, ‖f x‖ * (sqrt (ν x) * ‖∑ γ in Δ, c γ * conj (γ x)‖ ^ m)) ^ 2 := by
        simp_rw [mul_assoc]
      _ ≤ (∑ x, ‖f x‖ ^ 2) * ∑ x, (sqrt (ν x) * ‖∑ γ in Δ, c γ * conj (γ x)‖ ^ m) ^ 2 :=
        sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ ‖f‖_[2] ^ 2 * ∑ x, ν x * (‖∑ γ in Δ, c γ * conj (γ x)‖ ^ 2) ^ m := by
        simp_rw [l2Norm_sq_eq_sum, mul_pow, sq_sqrt (NNReal.coe_nonneg _), pow_right_comm]; rfl
  rw [mul_rotate', mul_left_comm, mul_pow, mul_pow, ←pow_mul', ←pow_mul', ←div_le_iff',
    mul_div_assoc, mul_div_assoc] at this
  calc
    _ ≤ _ := this
    _ = ‖(_ : ℂ)‖ := Eq.symm $ RCLike.norm_of_nonneg $ sum_nonneg fun _ _ ↦ by positivity
    _ = ‖∑ γ in Δ ^^ m, ∑ δ in Δ ^^ m,
          (∏ i, conj (c (γ i)) * c (δ i)) * conj (dft (fun a ↦ ν a) (∑ i, γ i - ∑ i, δ i))‖ := ?_
    _ ≤ ∑ γ in Δ ^^ m, ∑ δ in Δ ^^ m,
          ‖(∏ i, conj (c (γ i)) * c (δ i)) * conj (dft (fun a ↦ ν a) (∑ i, γ i - ∑ i, δ i))‖ :=
      (norm_sum_le _ _).trans $ sum_le_sum fun _ _ ↦ norm_sum_le _ _
    _ = _ := by simp [energy, norm_c, -Complex.norm_eq_abs, norm_prod]
  · push_cast
    simp_rw [←RCLike.conj_mul, dft_apply, l2Inner_eq_sum, map_sum, map_mul, RCLike.conj_conj,
      mul_pow, sum_pow', sum_mul, mul_sum, @sum_comm _ _ G, ←AddChar.inv_apply_eq_conj, ←
      AddChar.neg_apply', prod_mul_prod_comm, ←AddChar.add_apply, ←AddChar.sum_apply,
      mul_left_comm (Algebra.cast (ν _ : ℝ) : ℂ), ←mul_sum, ←sub_eq_add_neg, sum_sub_distrib,
      Complex.conj_ofReal, mul_comm]
    rfl
  positivity

lemma spec_hoelder (hη : 0 ≤ η) (hΔ : Δ ⊆ largeSpec f η) (hm : m ≠ 0) :
    ↑Δ.card ^ (2 * m) * (η ^ (2 * m) * α f) ≤ boringEnergy m Δ := by
  have hG : (0 : ℝ) < card G := by positivity
  simpa [boringEnergy, α, mul_assoc, ←Pi.one_def, ←mul_div_right_comm, ←mul_div_assoc,
    div_le_iff hG, energy_nsmul, -nsmul_eq_mul, ←nsmul_eq_mul'] using
    general_hoelder hη 1 (fun (_ : G) _ ↦ le_rfl) hΔ hm

noncomputable def changConst : ℝ := 32 * exp 1

lemma one_lt_changConst : 1 < changConst := one_lt_mul (by norm_num) $ one_lt_exp_iff.2 one_pos

lemma changConst_pos : 0 < changConst := zero_lt_one.trans one_lt_changConst

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `changConst` is positive. -/
@[positivity changConst] def evalChangConst : PositivityExt where eval _ _ _ := do
  return .positive (q(changConst_pos) : Lean.Expr)

example : 0 < changConst := by positivity

end Mathlib.Meta.Positivity

lemma AddDissociated.boringEnergy_le [DecidableEq G] {s : Finset G}
    (hs : AddDissociated (s : Set G)) (n : ℕ) :
    boringEnergy n s ≤ changConst ^ n * n ^ n * s.card ^ n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  calc
    _ = ‖dft (𝟭 s)‖ₙ_[↑(2 * n)] ^ (2 * n) := by rw [nlpNorm_dft_indicate_pow]
    _ ≤ (4 * rexp 2⁻¹ * sqrt ↑(2 * n) * ‖dft (𝟭 s)‖ₙ_[2]) ^ (2 * n) := by
        gcongr
        refine rudin_ineq (le_mul_of_one_le_right zero_le_two $ Nat.one_le_iff_ne_zero.2 hn)
          (dft (𝟭_[ℂ] s)) ?_
        rwa [cft_dft, support_comp_eq_preimage, support_indicate, Set.preimage_comp,
          Set.neg_preimage, addDissociated_neg, AddEquiv.addDissociated_preimage]
    _ = _ := by
        simp_rw [mul_pow, pow_mul, nl2Norm_dft_indicate]
        rw [← exp_nsmul, sq_sqrt, sq_sqrt]
        simp_rw [←mul_pow]
        simp [changConst]
        ring_nf
        all_goals positivity

/-- **Chang's lemma**. -/
lemma chang (hf : f ≠ 0) (hη : 0 < η) :
    ∃ Δ, Δ ⊆ largeSpec f η ∧
      Δ.card ≤ ⌈changConst * exp 1 * ⌈curlog (α f)⌉₊ / η ^ 2⌉₊ ∧ largeSpec f η ⊆ Δ.addSpan := by
  refine diss_addSpan fun Δ hΔη hΔ ↦ ?_
  obtain hΔ' | hΔ' := @eq_zero_or_pos _ _ Δ.card
  · simp [hΔ']
  have : 0 < α f := α_pos hf
  set β := ⌈curlog (α f)⌉₊
  have hβ : 0 < β := Nat.ceil_pos.2 (curlog_pos (α_pos hf) $ α_le_one _)
  refine' le_of_pow_le_pow_left hβ.ne' zero_le' $ Nat.cast_le.1 $ le_of_mul_le_mul_right _
    (by positivity : 0 < ↑Δ.card ^ β * (η ^ (2 * β) * α f))
  push_cast
  rw [←mul_assoc, ←pow_add, ←two_mul]
  refine' ((spec_hoelder hη.le hΔη hβ.ne').trans $ hΔ.boringEnergy_le _).trans _
  refine' le_trans _ $ mul_le_mul_of_nonneg_right (pow_le_pow_left _ (Nat.le_ceil _) _) _
  rw [mul_right_comm, div_pow, mul_pow, mul_pow, exp_one_pow, ←pow_mul, mul_div_assoc]
  calc
    _ = (changConst * Δ.card * β) ^ β := by ring
    _ ≤ (changConst * Δ.card * β) ^ β * (α f * exp β) := ?_
    _ ≤ (changConst * Δ.card * β) ^ β * ((η / η) ^ (2 * β) * α f * exp β) := by
        rw [div_self hη.ne', one_pow, one_mul]
    _ = _ := by ring
  refine' le_mul_of_one_le_right (by positivity) _
  rw [←inv_pos_le_iff_one_le_mul']
  exact inv_le_exp_curlog.trans $ exp_monotone $ Nat.le_ceil _
  all_goals positivity
