import Mathlib.Algebra.Order.Chebyshev
import LeanAPAP.Mathlib.Algebra.BigOperators.Order
import LeanAPAP.Mathlib.Algebra.BigOperators.Ring
import LeanAPAP.Mathlib.Analysis.MeanInequalities
import LeanAPAP.Mathlib.Data.Nat.Cast.Field
import LeanAPAP.Mathlib.Data.Nat.Order.Basic
import LeanAPAP.Mathlib.Data.Real.Sqrt
import LeanAPAP.Prereqs.DFT
import LeanAPAP.Prereqs.Energy
import LeanAPAP.Prereqs.Misc

/-!
# Chang's lemma
-/

open Finset Fintype Real

open scoped BigOperators ComplexConjugate ComplexOrder NNReal

variable {G : Type*} [AddCommGroup G] [Fintype G] {f : G → ℂ} {η : ℝ} {ψ : AddChar G ℂ}
  {Δ : Finset (AddChar G ℂ)} {m : ℕ}

/-- The `η`-large spectrum of a function. -/
noncomputable def largeSpec (f : G → ℂ) (η : ℝ) : Finset (AddChar G ℂ) :=
  univ.filter fun ψ ↦ η * ‖f‖_[1] ≤ ‖dft f ψ‖

@[simp]
lemma mem_largeSpec : ψ ∈ largeSpec f η ↔ η * ‖f‖_[1] ≤ ‖dft f ψ‖ := by simp [largeSpec]

lemma largeSpec_anti (f : G → ℂ) : Antitone (largeSpec f) := fun η ν h ψ ↦ by
  simp_rw [mem_largeSpec]; exact (mul_le_mul_of_nonneg_right h lpNorm_nonneg).trans

@[simp]
lemma largeSpec_zero_left (η : ℝ) : largeSpec (0 : G → ℂ) η = univ := by simp [largeSpec]

@[simp]
lemma largeSpec_zero_right (f : G → ℂ) : largeSpec f 0 = univ := by simp [largeSpec]

private noncomputable def α (f : G → ℂ) :=
  ‖f‖_[1] ^ 2 / ‖f‖_[2] ^ 2 / card G

lemma α_nonneg (f : G → ℂ) : 0 ≤ α f := by unfold α; positivity

lemma α_pos (hf : f ≠ 0) : 0 < α f := by unfold α; sorry -- positivity

lemma α_le_one (f : G → ℂ) : α f ≤ 1 := by
  refine' div_le_one_of_le (div_le_of_nonneg_of_le_mul _ _ _) _
  any_goals positivity
  rw [L1norm_eq_sum, l2norm_sq_eq_sum]
  exact sq_sum_le_card_mul_sum_sq

lemma general_hoelder (hη : 0 ≤ η) (ν : G → ℝ≥0) (hfν : ∀ x, f x ≠ 0 → 1 ≤ ν x)
    (hΔ : Δ ⊆ largeSpec f η) (hm : m ≠ 0) :
    ↑Δ.card ^ (2 * m) * (η ^ (2 * m) * (‖f‖_[1] ^ 2 / ‖f‖_[2] ^ 2)) ≤
      energy m Δ (dft fun a ↦ ν a) := by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  choose c norm_c hc using fun γ ↦ IsROrC.exists_norm_eq_mul_self (dft f γ)
  have :=
    calc
      η * ‖f‖_[1] * Δ.card ≤ ∑ γ in Δ, ‖dft f γ‖ := _
      _ ≤ ‖∑ x, f x * ∑ γ in Δ, c γ * conj (γ x)‖ := _
      _ ≤ ∑ x, ‖f x * ∑ γ in Δ, c γ * conj (γ x)‖ := (norm_sum_le _ _)
      _ = ∑ x, ‖f x‖ * ‖∑ γ in Δ, c γ * conj (γ x)‖ := by simp_rw [norm_mul]
      _ ≤ _ := (weighted_hoelder' m _ _ _ (fun _ ↦ norm_nonneg _) fun _ ↦ norm_nonneg _)
      _ = ‖f‖_[1] ^ (1 - m⁻¹ : ℝ) * (∑ x, ‖f x‖ * ‖∑ γ in Δ, c γ * conj (γ x)‖ ^ m) ^ (m⁻¹ : ℝ) :=
        by push_cast <;> simp_rw [L1norm_eq_sum, rpow_nat_cast]
  rotate_left
  · rw [←nsmul_eq_mul']
    exact card_nsmul_le_sum _ _ _ fun x hx ↦ mem_largeSpec.1 $ hΔ hx
  · simp_rw [mul_sum, mul_comm (f _), mul_assoc (c _), @sum_comm _ _ G, ←mul_sum, ←l2inner_eq_sum,
      ←dft_apply, ←hc, ←Complex.ofReal_sum, IsROrC.norm_ofReal]
    exact le_abs_self _
  · norm_cast
    exact hm.bot_lt
  replace this := pow_le_pow_of_le_left (by positivity) this m
  simp_rw [mul_pow] at this
  rw [rpow_nat_inv_pow_nat (sum_nonneg fun _ _ ↦ _) hm, ←rpow_mul_nat_cast, one_sub_mul,
    inv_mul_cancel, ←Nat.cast_pred, rpow_nat_cast, mul_assoc, mul_left_comm, ←pow_sub_one_mul,
    mul_assoc, mul_le_mul_left] at this
  any_goals positivity
  replace hfν : ∀ x, ‖f x‖ ≤ ‖f x‖ * sqrt (ν x)
  · rintro x
    obtain hfx | hfx := eq_or_ne (f x) 0
    · simp [hfx]
    ·
      exact
        le_mul_of_one_le_right (norm_nonneg _) (one_le_sqrt.2 $ NNReal.one_le_coe.2 $ hfν _ hfx)
  replace this :=
    calc
      _ ≤ (∑ x, ‖f x‖ * sqrt (ν x) * ‖∑ γ in Δ, c γ * conj (γ x)‖ ^ m) ^ 2 :=
        pow_le_pow_of_le_left (by positivity)
          (this.trans $ sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_right (hfν _) $ by positivity)
          _
      _ = (∑ x, ‖f x‖ * (sqrt (ν x) * ‖∑ γ in Δ, c γ * conj (γ x)‖ ^ m)) ^ 2 := by
        simp_rw [mul_assoc]
      _ ≤ (∑ x, ‖f x‖ ^ 2) * ∑ x, (sqrt (ν x) * ‖∑ γ in Δ, c γ * conj (γ x)‖ ^ m) ^ 2 :=
        (sum_mul_sq_le_sq_mul_sq _ _ _)
      _ ≤ ‖f‖_[2] ^ 2 * ∑ x, ν x * (‖∑ γ in Δ, c γ * conj (γ x)‖ ^ 2) ^ m := by
        simp_rw [l2norm_sq_eq_sum, mul_pow, sq_sqrt (NNReal.coe_nonneg _), pow_right_comm]
  rw [mul_rotate', mul_left_comm, mul_pow, mul_pow, ←pow_mul', ←pow_mul', ←div_le_iff',
    mul_div_assoc, mul_div_assoc] at this
  any_goals positivity
  calc
    _ ≤ _ := this
    _ = ‖(_ : ℂ)‖ := (Eq.symm $ IsROrC.norm_of_nonneg $ sum_nonneg fun _ _ ↦ by positivity)
    _ =
        ‖∑ γ in piFinset fun i : Fin m ↦ Δ,
            ∑ δ in piFinset fun i : Fin m ↦ Δ,
              (∏ i, conj (c (γ i)) * c (δ i)) * conj (dft (fun a ↦ ν a) (∑ i, γ i - ∑ i, δ i))‖ :=
      _
    _ ≤
        ∑ γ in piFinset fun i : Fin m ↦ Δ,
          ∑ δ in piFinset fun i : Fin m ↦ Δ,
            ‖(∏ i, conj (c (γ i)) * c (δ i)) * conj (dft (fun a ↦ ν a) (∑ i, γ i - ∑ i, δ i))‖ :=
      ((norm_sum_le _ _).trans $ sum_le_sum fun _ _ ↦ norm_sum_le _ _)
    _ = _ := by simp [energy, norm_c, -Complex.norm_eq_abs, norm_prod]
  · push_cast
    simp_rw [←IsROrC.conj_mul', dft_apply, l2inner_eq_sum, map_sum, map_mul, IsROrC.conj_conj,
      mul_pow, sum_pow', sum_mul, mul_sum, @sum_comm _ _ G, ←AddChar.inv_apply_eq_conj, ←
      AddChar.neg_apply', prod_mul_prod_comm, ←AddChar.add_apply, ←AddChar.sum_apply,
      mul_left_comm ((ν _ : ℝ) : ℂ), ←mul_sum, ←sub_eq_add_neg, sum_sub_distrib, coe_coe,
      IsROrC.conj_ofReal, mul_comm]

lemma spec_hoelder (hη : 0 ≤ η) (hΔ : Δ ⊆ largeSpec f η) (hm : m ≠ 0) :
    ↑Δ.card ^ (2 * m) * (η ^ (2 * m) * α f) ≤ boringEnergy m Δ := by
  have hG : (0 : ℝ) < card G := by sorry -- positivity
  simpa [boringEnergy, α, mul_assoc, ←Pi.one_def, ←mul_div_right_comm, ←mul_div_assoc,
    div_le_iff hG, energy_nsmul, -nsmul_eq_mul, ←nsmul_eq_mul'] using
    general_hoelder hη 1 (fun (_ : G) _ ↦ le_rfl) hΔ hm

/-- **Chang's lemma**. -/
lemma chang (hf : f ≠ 0) (hη : 0 < η) :
    ∃ Δ, Δ ⊆ largeSpec f η ∧
      Δ.card ≤ changConst * ⌈exp 1 * ⌈curlog (α f)⌉₊ / η ^ 2⌉₊ ∧ largeSpec f η ⊆ Δ.addSpan := by
  refine' diss_addSpan fun Δ hΔη hΔ ↦ _
  obtain hΔ' | hΔ' := @eq_zero_or_pos _ _ Δ.card
  · simp [hΔ']
  have : 0 < α f := α_pos hf
  set β := ⌈curlog (α f)⌉₊
  have hβ : 0 < β := Nat.ceil_pos.2 (curlog_pos (α_pos hf) $ α_le_one _)
  refine'
    le_of_pow_le_pow _ zero_le' hβ
      (Nat.cast_le.1 $
        le_of_mul_le_mul_right _ (by positivity : 0 < ↑Δ.card ^ β * (η ^ (2 * β) * α f)))
  push_cast
  rw [←mul_assoc, ←pow_add, ←two_mul, mul_pow, mul_mul_mul_comm]
  refine' ((spec_hoelder hη.le hΔη hβ.ne').trans $ hΔ.boring_energy_le _).trans _
  rw [mul_right_comm]
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  rw [←div_le_iff]
  refine' le_trans _ (pow_le_pow_of_le_left _ (Nat.le_ceil _) _)
  rw [div_pow, mul_pow, exp_one_pow, ←pow_mul, ←div_div, div_eq_inv_mul, mul_div_assoc]
  exact
    mul_le_mul_of_nonneg_right (inv_le_exp_curlog.trans $ exp_monotone $ Nat.le_ceil _)
      (by positivity)
  all_goals positivity
