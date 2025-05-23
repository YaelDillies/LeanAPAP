import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Bound
import LeanAPAP.Prereqs.Energy
import LeanAPAP.Prereqs.LargeSpec
import LeanAPAP.Prereqs.Rudin

/-!
# Chang's lemma
-/

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ComplexOrder NNReal

variable {G : Type*} [AddCommGroup G] [Fintype G] {f : G → ℂ} {x η : ℝ} {ψ : AddChar G ℂ}
  {Δ : Finset (AddChar G ℂ)} {m : ℕ}

local notation "𝓛" x:arg => 1 + log x⁻¹

private lemma curlog_pos (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : 0 < 𝓛 x := by
  obtain rfl | hx₀ := hx₀.eq_or_lt
  · simp
  have : 0 ≤ log x⁻¹ := by bound
  positivity

private lemma rpow_inv_neg_curlog_le (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : x⁻¹ ^ (𝓛 x)⁻¹ ≤ exp 1 := by
  obtain rfl | hx₀ := hx₀.eq_or_lt
  · simp; positivity
  obtain rfl | hx₁ := hx₁.eq_or_lt
  · simp
  have hx := (one_lt_inv₀ hx₀).2 hx₁
  calc
    x⁻¹ ^ (𝓛 x)⁻¹ ≤ x⁻¹ ^ (log x⁻¹)⁻¹ := by
      gcongr
      · exact hx.le
      · exact log_pos hx
      · simp
    _ ≤ exp 1 := x⁻¹.rpow_inv_log_le_exp_one

noncomputable def changConst : ℝ := 32 * exp 1

lemma one_lt_changConst : 1 < changConst := by unfold changConst; bound

lemma changConst_pos : 0 < changConst := zero_lt_one.trans one_lt_changConst

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `changConst` is positive. -/
@[positivity changConst] def evalChangConst : PositivityExt where eval _ _ _ := do
  return .positive (q(changConst_pos) : Lean.Expr)

example : 0 < changConst := by positivity

end Mathlib.Meta.Positivity

lemma AddDissociated.boringEnergy_le [MeasurableSpace G] [DiscreteMeasurableSpace G] [DecidableEq G]
    {s : Finset G} (hs : AddDissociated (s : Set G)) (n : ℕ) :
    boringEnergy n s ≤ changConst ^ n * n ^ n * #s ^ n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  calc
    _ = (‖dft (𝟭 s)‖ₙ_[↑(2 * n)] ^ (2 * n) : ℝ) := by rw [cLpNorm_dft_indicate_pow]
    _ ≤ (4 * rexp 2⁻¹ * sqrt ↑(2 * n) * ‖dft (𝟭 s)‖ₙ_[2]) ^ (2 * n) := by
        gcongr
        refine rudin_ineq (le_mul_of_one_le_right zero_le_two <| Nat.one_le_iff_ne_zero.2 hn)
          (dft (𝟭_[ℂ] s)) ?_
        rwa [cft_dft, support_comp_eq_preimage, support_indicate, Set.preimage_comp,
          Set.neg_preimage, addDissociated_neg, AddEquiv.addDissociated_preimage]
    _ = _ := by
        simp_rw [mul_pow, pow_mul, cL2Norm_dft_indicate]
        rw [← exp_nsmul, sq_sqrt (by positivity), sq_sqrt (by positivity)]
        simp_rw [← mul_pow]
        simp [changConst]
        ring_nf

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

lemma general_hoelder (hη : 0 ≤ η) (ν : G → ℝ≥0) (hfν : ∀ x, f x ≠ 0 → 1 ≤ ν x)
    (hΔ : Δ ⊆ largeSpec f η) (hm : m ≠ 0) :
    #Δ ^ (2 * m) * (η ^ (2 * m) * (‖f‖ₙ_[1] ^ 2 / ‖f‖ₙ_[2] ^ 2)) ≤
      energy m Δ (cft fun a ↦ ν a) := by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  choose c norm_c hc using fun γ ↦ RCLike.exists_norm_eq_mul_self (cft f γ)
  have :=
    calc
      η * ‖f‖ₙ_[1] * Δ.card ≤ ∑ γ ∈ Δ, ‖cft f γ‖ := by
        rw [← nsmul_eq_mul']
        exact card_nsmul_le_sum _ _ _ fun x hx ↦ mem_largeSpec_iff_cft.1 <| hΔ hx
      _ ≤ |∑ i ∈ Δ, ‖cft f i‖| := le_abs_self _
      _ = ‖𝔼 x, f x * ∑ γ ∈ Δ, c γ * conj (γ x)‖ := by
        simp_rw [mul_sum, mul_comm (f _), mul_assoc (c _), expect_sum_comm, ← mul_expect,
          ← cL2Inner_eq_expect, ← cft_apply, ← hc, ← RCLike.ofReal_sum, RCLike.norm_ofReal]
      _ ≤ 𝔼 x, ‖f x * ∑ γ ∈ Δ, c γ * conj (γ x)‖ := norm_expect_le (K := ℂ)
      _ = 𝔼 x, ‖f x‖ * ‖∑ γ ∈ Δ, c γ * conj (γ x)‖ := by simp_rw [norm_mul]
      _ ≤ _ :=
        compact_inner_le_weight_mul_Lp_of_nonneg _ (p := m) (mod_cast hm.bot_lt)
          (fun _ ↦ norm_nonneg _) fun _ ↦ norm_nonneg _
      _ = ‖f‖ₙ_[1] ^ (1 - (m : ℝ)⁻¹) * (𝔼 x, ‖f x‖ * ‖∑ γ ∈ Δ, c γ * conj (γ x)‖ ^ m) ^ (m⁻¹ : ℝ) :=
        by simp_rw [cL1Norm_eq_expect_norm, rpow_natCast]
  replace hfν : ∀ x, ‖f x‖ ≤ ‖f x‖ * sqrt (ν x) := by
    rintro x
    obtain hfx | hfx := eq_or_ne (f x) 0
    · simp [hfx]
    · exact le_mul_of_one_le_right (norm_nonneg _) <| one_le_sqrt.2 <| NNReal.one_le_coe.2 <|
        hfν _ hfx
  have :=
    calc
      (‖f‖ₙ_[1] * (η ^ m * Δ.card ^ m)) ^ 2
        = (‖f‖ₙ_[1] / ‖f‖ₙ_[1] ^ m * ‖f‖ₙ_[1] ^ m * (η ^ m * Δ.card ^ m)) ^ 2 := by
        rw [div_mul_cancel₀]; positivity
      _ = (‖f‖ₙ_[1] ^ (1 - m : ℤ) * (η * ‖f‖ₙ_[1] * Δ.card) ^ m) ^ 2 := by
        rw [zpow_one_sub_natCast₀]; ring; positivity
      _ ≤ (‖f‖ₙ_[1] ^ (1 - m : ℤ) * (‖f‖ₙ_[1] ^ (1 - (m : ℝ)⁻¹) *
            (𝔼 x, ‖f x‖ * ‖∑ γ ∈ Δ, c γ * conj (γ x)‖ ^ m) ^ (m⁻¹ : ℝ)) ^ m) ^ 2 := by gcongr
      _ = (‖f‖ₙ_[1] ^ (1 - m : ℤ) * (‖f‖ₙ_[1] ^ (m - 1 : ℤ) *
            𝔼 x, ‖f x‖ * ‖∑ γ ∈ Δ, c γ * conj (γ x)‖ ^ m)) ^ 2 := by
        rw [mul_pow _ _ m, ← rpow_mul_natCast, ← rpow_mul_natCast, one_sub_mul, inv_mul_cancel₀]
        norm_cast
        ring
        all_goals positivity
      _ = (𝔼 x, ‖f x‖ * ‖∑ γ ∈ Δ, c γ * conj (γ x)‖ ^ m) ^ 2 := by
        rw [← mul_assoc, ← zpow_add₀]; simp; positivity
      _ ≤ (𝔼 x, ‖f x‖ * sqrt (ν x) * ‖∑ γ ∈ Δ, c γ * conj (γ x)‖ ^ m) ^ 2 := by gcongr; exact hfν _
      _ = (𝔼 x, ‖f x‖ * (sqrt (ν x) * ‖∑ γ ∈ Δ, c γ * conj (γ x)‖ ^ m)) ^ 2 := by
        simp_rw [mul_assoc]
      _ ≤ (𝔼 x, ‖f x‖ ^ 2) * 𝔼 x, (sqrt (ν x) * ‖∑ γ ∈ Δ, c γ * conj (γ x)‖ ^ m) ^ 2 :=
        expect_mul_sq_le_sq_mul_sq ..
      _ ≤ ‖f‖ₙ_[2] ^ 2 * 𝔼 x, ν x * (‖∑ γ ∈ Δ, c γ * conj (γ x)‖ ^ 2) ^ m := by
        simp_rw [cL2Norm_sq_eq_expect_norm, mul_pow, sq_sqrt (NNReal.coe_nonneg _), pow_right_comm]
        rfl
  rw [mul_rotate', mul_left_comm, mul_pow, mul_pow, ← pow_mul', ← pow_mul', ← div_le_iff₀',
    mul_div_assoc, mul_div_assoc] at this
  calc
    Δ.card ^ (2 * m) * (η ^ (2 * m) * (‖f‖ₙ_[1] ^ 2 / ‖f‖ₙ_[2] ^ 2))
      ≤ 𝔼 x, ν x * (‖∑ γ ∈ Δ, c γ * conj (γ x)‖ ^ 2) ^ m := this
    _ = ‖(_ : ℂ)‖ := Eq.symm <| RCLike.norm_of_nonneg <| by positivity
    _ = ‖∑ γ ∈ Δ ^^ m, ∑ δ ∈ Δ ^^ m,
          (∏ i, conj (c (γ i)) * c (δ i)) * conj (cft (fun a ↦ ν a) (∑ i, γ i - ∑ i, δ i))‖ := ?_
    _ ≤ ∑ γ ∈ Δ ^^ m, ∑ δ ∈ Δ ^^ m,
          ‖(∏ i, conj (c (γ i)) * c (δ i)) * conj (cft (fun a ↦ ν a) (∑ i, γ i - ∑ i, δ i))‖ :=
      (norm_sum_le _ _).trans <| sum_le_sum fun _ _ ↦ norm_sum_le _ _
    _ = _ := by simp [energy, norm_c, norm_prod]
  · push_cast
    simp_rw [← RCLike.conj_mul, cft_apply, cL2Inner_eq_expect', map_sum, map_mul, RCLike.conj_conj,
      mul_pow, sum_pow', sum_mul, mul_sum, expect_sum_comm, ← AddChar.inv_apply_eq_conj,
      ← AddChar.neg_apply', prod_mul_prod_comm, ← AddChar.add_apply, ← AddChar.sum_apply,
      map_expect, mul_left_comm (Algebra.cast (ν _ : ℝ) : ℂ), ← mul_expect, ← sub_eq_add_neg,
      sum_sub_distrib, map_mul, Complex.conj_ofReal, mul_comm (Algebra.cast (ν _ : ℝ) : ℂ),
      ← AddChar.map_neg_eq_conj, AddChar.neg_apply, neg_neg]
    rfl

open scoped ComplexOrder

lemma spec_hoelder (hη : 0 ≤ η) (hΔ : Δ ⊆ largeSpec f η) (hm : m ≠ 0) :
    #Δ ^ (2 * m) * (η ^ (2 * m) * (‖f‖ₙ_[1] ^ 2 / ‖f‖ₙ_[2] ^ 2)) ≤ boringEnergy m Δ := by
  have hG : (0 : ℝ) < card G := by positivity
  simpa [boringEnergy, mul_assoc, ← Pi.one_def, ← mul_div_right_comm, ← mul_div_assoc,
    div_le_iff₀ hG, energy_nsmul, -nsmul_eq_mul, ← nsmul_eq_mul'] using
    general_hoelder hη 1 (fun (_ : G) _ ↦ le_rfl) hΔ hm

/-- **Chang's lemma**. -/
lemma chang (hf : f ≠ 0) (hη : 0 < η) :
    ∃ Δ, Δ ⊆ largeSpec f η ∧ largeSpec f η ⊆ Δ.addSpan ∧
      #Δ ≤ ⌈changConst * exp 1 * ⌈𝓛 ↑(‖f‖ₙ_[1] ^ 2 / ‖f‖ₙ_[2] ^ 2)⌉₊ / η ^ 2⌉₊ := by
  simp_rw [and_comm (a := largeSpec f η ⊆ _)]
  refine exists_subset_addSpan_card_le_of_forall_addDissociated fun Δ hΔη hΔ ↦ ?_
  obtain hΔ' | hΔ' := eq_zero_or_pos #Δ
  · simp [hΔ']
  let α := ‖f‖ₙ_[1] ^ 2 / ‖f‖ₙ_[2] ^ 2
  have : 0 < α := by positivity
  set β := ⌈𝓛 α⌉₊
  have hβ : 0 < β := Nat.ceil_pos.2 <| curlog_pos (by positivity) <|
    div_le_one_of_le₀ (by dsimp; gcongr; exact one_le_two) (by dsimp; positivity)
  have : 0 < ‖f‖ₙ_[1] := by positivity
  refine le_of_pow_le_pow_left₀ hβ.ne' zero_le' <| Nat.cast_le.1 <| le_of_mul_le_mul_right ?_
    (by positivity : 0 < Δ.card ^ β * (η ^ (2 * β) * α))
  push_cast
  rw [← mul_assoc, ← pow_add, ← two_mul]
  refine ((spec_hoelder hη.le hΔη hβ.ne').trans <| hΔ.boringEnergy_le _).trans ?_
  refine le_trans ?_ <| mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ?_ (Nat.le_ceil _) _) ?_
  any_goals positivity
  rw [mul_right_comm, div_pow, mul_pow, mul_pow, exp_one_pow, ← pow_mul, mul_div_assoc]
  calc
    _ = (changConst * #Δ * β) ^ β := by ring
    _ ≤ (changConst * #Δ * β) ^ β * (α * exp β) := ?_
    _ ≤ (changConst * #Δ * β) ^ β * ((η / η) ^ (2 * β) * α * exp β) := by
      rw [div_self hη.ne', one_pow, one_mul]
    _ = _ := by ring
  refine le_mul_of_one_le_right (by positivity) ?_
  rw [← inv_le_iff_one_le_mul₀' (by positivity)]
  calc
    α⁻¹ = exp (0 + log α⁻¹) := by
      rw [zero_add, exp_log]
      · norm_cast
      · positivity
    _ ≤ exp ⌈0 + log α⁻¹⌉₊ := by gcongr; exact Nat.le_ceil _
    _ ≤ exp β := by unfold β; gcongr; exact zero_le_one
