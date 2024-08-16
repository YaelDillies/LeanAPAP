import LeanAPAP.Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanAPAP.Mathlib.Data.Finset.Density
import LeanAPAP.Mathlib.Data.Nat.Cast.Order.Basic
import LeanAPAP.Mathlib.Data.Rat.Cast.Order
import LeanAPAP.Mathlib.Data.ZMod.Basic
import LeanAPAP.Prereqs.Convolution.ThreeAP
import LeanAPAP.Prereqs.FourierTransform.Compact
import LeanAPAP.Prereqs.LargeSpec
import LeanAPAP.Physics.AlmostPeriodicity
import LeanAPAP.Physics.Unbalancing

/-!
# Finite field case
-/

open FiniteDimensional Finset Fintype Function Real
open scoped NNReal BigOperators Combinatorics.Additive Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] {A C : Finset G} {γ ε : ℝ}

lemma global_dichotomy (hA : A.Nonempty) (hγC : γ ≤ C.dens) (hγ : 0 < γ)
    (hAC : ε ≤ |card G * ⟪μ A ∗ μ A, μ C⟫_[ℝ] - 1|) :
    ε / (2 * card G) ≤
      ‖balance (μ_[ℝ] A) ○ balance (μ A)‖_[↑(2 * ⌈γ.curlog⌉₊), const _ (card G)⁻¹] := by
  have hC : C.Nonempty := by simpa using hγ.trans_le hγC
  have hγ₁ : γ ≤ 1 := hγC.trans (by norm_cast; exact dens_le_one)
  set p := 2 * ⌈γ.curlog⌉₊
  have hp : 1 < p :=
    Nat.succ_le_iff.1 (le_mul_of_one_le_right zero_le' $ Nat.ceil_pos.2 $ curlog_pos hγ hγ₁)
  have hp' : (p⁻¹ : ℝ≥0) < 1 := inv_lt_one $ mod_cast hp
  have hp'' : (p : ℝ≥0).IsConjExponent _ := .conjExponent $ mod_cast hp
  rw [mul_comm, ← div_div, div_le_iff (zero_lt_two' ℝ)]
  calc
    _ ≤ _ := div_le_div_of_nonneg_right hAC (card G).cast_nonneg
    _ = |⟪balance (μ A) ∗ balance (μ A), μ C⟫_[ℝ]| := ?_
    _ ≤ ‖balance (μ_[ℝ] A) ∗ balance (μ A)‖_[p] * ‖μ_[ℝ] C‖_[NNReal.conjExponent p] :=
        abs_l2Inner_le_lpNorm_mul_lpNorm hp'' _ _
    _ ≤ ‖balance (μ_[ℝ] A) ○ balance (μ A)‖_[p] * (card G ^ (-(p : ℝ)⁻¹) * γ ^ (-(p : ℝ)⁻¹)) :=
        mul_le_mul (lpNorm_conv_le_lpNorm_dconv' (by positivity) (even_two_mul _) _) ?_
          (by positivity) (by positivity)
    _ = ‖balance (μ_[ℝ] A) ○ balance (μ A)‖_[↑(2 * ⌈γ.curlog⌉₊), const _ (card G)⁻¹] *
          γ ^ (-(p : ℝ)⁻¹) := ?_
    _ ≤ _ := mul_le_mul_of_nonneg_left ?_ $ by positivity
  · rw [← balance_conv, balance, l2Inner_sub_left, l2Inner_const_left, expect_conv, sum_mu ℝ hA,
      expect_mu ℝ hA, sum_mu ℝ hC, conj_trivial, one_mul, mul_one, ← mul_inv_cancel₀, ← mul_sub,
      abs_mul, abs_of_nonneg, mul_div_cancel_left₀] <;> positivity
  · rw [lpNorm_mu hp''.symm.one_le hC, hp''.symm.coe.inv_sub_one, NNReal.coe_natCast, ← mul_rpow]
    rw [cast_dens, le_div_iff, mul_comm] at hγC
    refine rpow_le_rpow_of_nonpos ?_ hγC (neg_nonpos.2 ?_)
    all_goals positivity
  · simp_rw [Nat.cast_mul, Nat.cast_two, p]
    rw [wlpNorm_const_right, mul_assoc, mul_left_comm, NNReal.coe_inv, inv_rpow, rpow_neg]
    push_cast
    any_goals norm_cast; rw [Nat.succ_le_iff]
    rfl
    all_goals positivity
  · dsimp [p]
    push_cast
    norm_num
    rw [← neg_mul, rpow_mul, one_div, rpow_inv_le_iff_of_pos]
    exact (rpow_le_rpow_of_exponent_ge hγ hγ₁ $ neg_le_neg $
      inv_le_inv_of_le (curlog_pos hγ hγ₁) $ Nat.le_ceil _).trans $
        (rpow_neg_inv_curlog_le hγ.le hγ₁).trans $ exp_one_lt_d9.le.trans $ by norm_num
    all_goals positivity

variable {q n : ℕ} [Module (ZMod q) G] {A₁ A₂ : Finset G} (S : Finset G) {α : ℝ}

lemma ap_in_ff (hS : S.Nonempty) (hα₀ : 0 < α) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hαA₁ : α ≤ A₁.dens)
    (hαA₂ : α ≤ A₂.dens) :
    ∃ (V : Submodule (ZMod q) G) (V' : Finset G),
      (V : Set G) = V' ∧
        ↑(finrank (ZMod q) G - finrank (ZMod q) V) ≤
            2 ^ 27 * α.curlog ^ 2 * (ε * α).curlog ^ 2 / ε ^ 2 ∧
          |∑ x in S, (μ V' ∗ μ A₁ ∗ μ A₂) x - ∑ x in S, (μ A₁ ∗ μ A₂) x| ≤ ε := by
  classical
  have hA₁ : A₁.Nonempty := by simpa using hα₀.trans_le hαA₁
  have hA₂ : A₂.Nonempty := by simpa using hα₀.trans_le hαA₂
  have hA₁ : σ[A₁, univ] ≤ α⁻¹ :=
    calc
      _ ≤ (A₁.dens⁻¹ : ℝ) := by norm_cast; exact addConst_le_inv_dens
      _ ≤ α⁻¹ := by gcongr
  obtain ⟨T, hST, hT⟩ := AlmostPeriodicity.linfty_almost_periodicity_boosted ε hε₀ hε₁
    ⌈(ε * α / 4).curlog⌉₊ (Nat.ceil_pos.2 $ curlog_pos (by positivity) sorry).ne' sorry hA₁
    univ_nonempty S A₂ hS hA₂
  let Δ := largeSpec (μ T) 2⁻¹
  let V : AddSubgroup G := ⨅ γ ∈ Δ, γ.toAddMonoidHom.ker
  let V' : Finset G := Set.toFinset V
  have : ⟪μ V' ∗ μ A₁ ∗ μ A₂, 𝟭 S⟫_[ℝ] = 𝔼 v ∈ V', (μ A₁ ∗ μ A₂ ○ 𝟭 S) v := by
    calc
      _ = ⟪μ V', μ A₁ ∗ μ A₂ ○ 𝟭 S⟫_[ℝ] := by
        sorry
        -- rw [conv_assoc, conv_l2Inner, ← conj_l2Inner]
        -- simp

      _ = _ := sorry
  sorry

lemma di_in_ff (hε₀ : 0 < ε) (hε₁ : ε < 1) (hαA : α ≤ A.dens) (hγC : γ ≤ C.dens)
    (hγ : 0 < γ) (hAC : ε ≤ |card G * ⟪μ A ∗ μ A, μ C⟫_[ℝ] - 1|) :
    ∃ (V : Submodule (ZMod q) G) (V' : Finset G),
      (V : Set G) = V' ∧
        ↑(finrank (ZMod q) G - finrank (ZMod q) V) ≤
            2 ^ 171 * α.curlog ^ 4 * γ.curlog ^ 4 / ε ^ 24 ∧
          (1 + ε / 32) * α ≤ ‖𝟭_[ℝ] A * μ V'‖_[⊤] := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · stop
    refine ⟨⊤, univ, _⟩
    rw [AffineSubspace.direction_top]
    simp only [AffineSubspace.top_coe, coe_univ, eq_self_iff_true, finrank_top, tsub_self,
      Nat.cast_zero, indicate_empty, zero_mul, lpNorm_zero, true_and_iff,
      Finset.card_empty, zero_div] at hαA ⊢
    exact ⟨by positivity, mul_nonpos_of_nonneg_of_nonpos (by positivity) hαA⟩
  have hγ₁ : γ ≤ 1 := hγC.trans (by norm_cast; exact dens_le_one)
  have hG : (card G : ℝ) ≠ 0 := by positivity
  have := unbalancing _ (mul_ne_zero two_ne_zero (Nat.ceil_pos.2 $ curlog_pos hγ hγ₁).ne') (ε / 2)
    (by positivity) (div_le_one_of_le (hε₁.le.trans $ by norm_num) $ by norm_num)
    (const _ (card G)⁻¹) (card G • (balance (μ A) ○ balance (μ A)))
    (sqrt (card G) • balance (μ A)) (const _ (card G)⁻¹) ?_ ?_ ?_ ?_
  rotate_left
  · stop
    ext a : 1
    simp [smul_dconv, dconv_smul, smul_smul]
  · simp [card_univ, show (card G : ℂ) ≠ 0 by sorry]
  · simp only [comp_const, Nonneg.coe_inv, NNReal.coe_natCast]
    rw [← ENNReal.coe_one, lpNorm_const one_ne_zero]
    sorry
    -- simp only [Nonneg.coe_one, inv_one, rpow_one, norm_inv, norm_coe_nat,
    --   mul_inv_cancel₀ (show (card G : ℝ) ≠ 0 by positivity)]
  · have hγ' : (1 : ℝ≥0) ≤ 2 * ⌈γ.curlog⌉₊ := sorry
    sorry
    -- simpa [wlpNorm_nsmul hγ', ← nsmul_eq_mul, div_le_iff' (show (0 : ℝ) < card G by positivity),
    --   ← div_div, *] using global_dichotomy hA hγC hγ hAC
  sorry

theorem ff (hq : 3 ≤ q) {A : Finset G} (hA₀ : A.Nonempty) (hA : ThreeAPFree (α := G) A) :
    finrank (ZMod q) G ≤ curlog A.dens ^ 9 := by
  obtain hα | hα := le_total (q ^ (finrank (ZMod q) G / 2 : ℝ) : ℝ) (2 * (A.dens : ℝ)⁻¹ ^ 2)
  · rw [rpow_le_iff_le_log, log_mul, log_pow, Nat.cast_two, ← mul_div_right_comm,
      mul_div_assoc, ← le_div_iff] at hα
    calc
      _ ≤ (log 2 + 2 * log A.dens⁻¹) / (log q / 2) := hα
      _ = 4 / log q * (log A.dens⁻¹ + log 2 / 2) := by ring
      _ ≤ (0 + 2) ^ 8 * (log A.dens⁻¹ + 2) := by
        gcongr
        · exact add_nonneg (log_nonneg $ one_le_inv (by positivity) (mod_cast dens_le_one))
            (div_nonneg (log_nonneg (by norm_num)) (by norm_num))
        · calc
            4 / log q ≤ 4 / log 3 := by gcongr; assumption_mod_cast
            _ ≤ 4 / log 2 := by gcongr; norm_num
            _ ≤ 4 / 0.6931471803 := by gcongr; exact log_two_gt_d9.le
            _ ≤ (0 + 2) ^ 8 := by norm_num
        · calc
            log 2 / 2 ≤ 0.6931471808 / 2 := by gcongr; exact log_two_lt_d9.le
            _ ≤ 2 := by norm_num
      _ ≤ (log A.dens⁻¹ + 2) ^ 8 * (log A.dens⁻¹ + 2) := by
        gcongr
        sorry
        sorry
      _ = curlog A.dens ^ 9 := by rw [curlog_eq_log_inv_add_two, pow_succ _ 8]; positivity
    any_goals positivity
    sorry
  have ind (i : ℕ) :
    ∃ (V : Submodule (ZMod q) G) (_ : DecidablePred (· ∈ V)) (B : Finset V) (x : G),
      finrank (ZMod q) G ≤ finrank (ZMod q) V + i * curlog A.dens ^ 8 ∧ ThreeAPFree (B : Set V) ∧
      A.dens ≤ B.dens ∧
      (B.dens < (65 / 64 : ℝ) ^ i * A.dens →
        2⁻¹ ≤ card V * ⟪μ B ∗ μ B, μ (B.image (2 • ·))⟫_[ℝ]) := by
    induction' i with i ih hi
    · exact ⟨⊤, Classical.decPred _, A.map (Equiv.subtypeUnivEquiv (by simp)).symm.toEmbedding, 0,
        by simp, sorry, by simp,
        by simp [cast_dens, Fintype.card_subtype, subset_iff]⟩
    obtain ⟨V, _, B, x, hV, hB, hαβ, hBV⟩ := ih
    obtain hB' | hB' := le_or_lt 2⁻¹ (card V * ⟪μ B ∗ μ B, μ (B.image (2 • ·))⟫_[ℝ])
    · exact ⟨V, inferInstance, B, x, hV.trans (by gcongr; exact i.le_succ), hB, hαβ, fun _ ↦ hB'⟩
    sorry
    -- have := di_in_ff (by positivity) one_half_lt_one _ _ _ _
  obtain ⟨V, _, B, x, hV, hB, hαβ, hBV⟩ := ind ⌊curlog A.dens / log (65 / 64)⌋₊
  have aux : 0 < log (65 / 64) := log_pos (by norm_num)
  specialize hBV $ by
    calc
      _ ≤ (1 : ℝ) := mod_cast dens_le_one
      _ < _ := ?_
    rw [← inv_pos_lt_iff_one_lt_mul, lt_pow_iff_log_lt, ← div_lt_iff]
    calc
      log A.dens⁻¹ / log (65 / 64)
        < ⌊log A.dens⁻¹ / log (65 / 64)⌋₊ + 1 := Nat.lt_floor_add_one _
      _ = ⌊(log A.dens⁻¹ + log (65 / 64)) / log (65 / 64)⌋₊ := by
        rw [← div_add_one aux.ne', Nat.floor_add_one, Nat.cast_succ]
        exact div_nonneg (log_nonneg $ one_le_inv (by positivity) (by simp)) aux.le
      _ ≤ ⌊curlog A.dens / log (65 / 64)⌋₊ := by
        rw [curlog_eq_log_inv_add_two]
        gcongr
        · calc
            log (65 / 64) ≤ log 2 := by gcongr; norm_num
            _ ≤ 0.6931471808 := log_two_lt_d9.le
            _ ≤ 2 := by norm_num
        · positivity
    all_goals positivity
  rw [hB.l2Inner_mu_conv_mu_mu_two_smul_mu] at hBV
  sorry
  sorry
