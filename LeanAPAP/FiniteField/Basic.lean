import Project.Physics.Unbalancing
import Project.Prereqs.Convolution.Norm
import Project.Prereqs.Dft
import Project.Prereqs.Misc

#align_import finite_field.basic

/-!
# Finite field case
-/


open FiniteDimensional Finset Fintype Function Real

open scoped BigOperators NNReal

variable {G : Type _} [AddCommGroup G] [DecidableEq G] [Fintype G] {A C : Finset G} {γ ε : ℝ}

theorem global_dichotomy (hA : A.Nonempty) (hγC : γ ≤ C.card / card G) (hγ : 0 < γ)
    (hAC : ε ≤ |card G * ⟪μ A ∗ μ A, μ C⟫_[ℝ] - 1|) :
    ε / (2 * card G) ≤
      ‖balance (μ_[ℝ] A) ○ balance (μ A)‖_[↑(2 * ⌈γ.curlog⌉₊), const _ (card G)⁻¹] :=
  by
  have hC : C.nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    simpa [hγ.not_le] using hγC
  have hγ₁ : γ ≤ 1 := hγC.trans (div_le_one_of_le (Nat.cast_le.2 C.card_le_univ) <| by positivity)
  set p := 2 * ⌈γ.curlog⌉₊
  have hp : 1 < p :=
    Nat.succ_le_iff.1 (le_mul_of_one_le_right zero_le' <| Nat.ceil_pos.2 <| curlog_pos hγ hγ₁)
  have hp' : (p⁻¹ : ℝ≥0) < 1 := inv_lt_one (by exact_mod_cast hp)
  rw [mul_comm, ← div_div, div_le_iff (zero_lt_two' ℝ)]
  calc
    _ ≤ _ := div_le_div_of_le (card G).cast_nonneg hAC
    _ = |⟪balance (μ A) ∗ balance (μ A), μ C⟫_[ℝ]| := _
    _ ≤ ‖balance (μ_[ℝ] A) ∗ balance (μ A)‖_[p] * ‖μ_[ℝ] C‖_[↑(1 - p⁻¹ : ℝ≥0)⁻¹] :=
      (abs_l2inner_le_lpnorm_hMul_lpnorm ⟨by exact_mod_cast hp, _⟩ _ _)
    _ ≤ ‖balance (μ_[ℝ] A) ○ balance (μ A)‖_[p] * (card G ^ (-p⁻¹ : ℝ) * γ ^ (-p⁻¹ : ℝ)) :=
      (mul_le_mul (lpnorm_conv_le_lpnorm_dconv' (by positivity) (even_two_mul _) _) _
        (by positivity) (by positivity))
    _ =
        ‖balance (μ_[ℝ] A) ○ balance (μ A)‖_[↑(2 * ⌈γ.curlog⌉₊), const _ (card G)⁻¹] *
          γ ^ (-p⁻¹ : ℝ) :=
      _
    _ ≤ _ := mul_le_mul_of_nonneg_left _ <| by positivity
  ·
    rw [← balance_conv, balance, l2inner_sub_left, l2inner_const_left, expect_conv, sum_mu ℝ hA,
        expect_mu ℝ hA, sum_mu ℝ hC, conj_trivial, one_mul, mul_one, ← mul_inv_cancel, ← mul_sub,
        abs_mul, abs_of_nonneg, mul_div_cancel_left] <;>
      positivity
  · rw [NNReal.coe_inv, NNReal.coe_sub hp'.le]
    simp
  · rw [lpnorm_mu (one_le_inv (tsub_pos_of_lt hp') tsub_le_self) hC, NNReal.coe_inv,
      NNReal.coe_sub hp'.le, NNReal.coe_one, inv_inv, sub_sub_cancel_left, ← mul_rpow]
    rw [le_div_iff, mul_comm] at hγC 
    refine' rpow_le_rpow_of_nonpos _ hγC (neg_nonpos.2 _)
    all_goals positivity
  · simp_rw [Nat.cast_mul, Nat.cast_two]
    rw [wLpnorm_const_right, mul_assoc, mul_left_comm, NNReal.coe_inv, inv_rpow, rpow_neg]
    push_cast
    any_goals norm_cast; rw [Nat.succ_le_iff]
    all_goals positivity
  · push_cast
    norm_num
    rw [← neg_mul, rpow_mul, one_div, rpow_inv_le_iff_of_pos]
    refine'
      (rpow_le_rpow_of_exponent_ge hγ hγ₁ <|
            neg_le_neg <| inv_le_inv_of_le (curlog_pos hγ hγ₁) <| Nat.le_ceil _).trans
        ((rpow_neg_inv_curlog hγ.le hγ₁).trans <| exp_one_lt_d9.le.trans <| by norm_num)
    all_goals positivity

variable {q n : ℕ} [Module (ZMod q) G] {A₁ A₂ : Finset G} (S : Finset G) {α : ℝ}

theorem ap_in_ff (hA₁ : α ≤ A₁.card / card G) (hA₂ : α ≤ A₂.card / card G) :
    ∃ (V : AffineSubspace (ZMod q) G) (V' : Finset G),
      (V : Set G) = V' ∧
        ↑(finrank (ZMod q) G - finrank (ZMod q) V.direction) ≤
            2 ^ 27 * α.curlog ^ 2 * (ε * α).curlog ^ 2 / ε ^ 2 ∧
          |∑ x in S, (μ V' ∗ μ A₁ ∗ μ A₂) x - ∑ x in S, (μ A₁ ∗ μ A₂) x| ≤ ε :=
  sorry

theorem di_in_ff (hε₀ : 0 < ε) (hε₁ : ε < 1) (hαA : α ≤ A.card / card G) (hγC : γ ≤ C.card / card G)
    (hγ : 0 < γ) (hAC : ε ≤ |card G * ⟪μ A ∗ μ A, μ C⟫_[ℝ] - 1|) :
    ∃ (V : AffineSubspace (ZMod q) G) (V' : Finset G),
      (V : Set G) = V' ∧
        ↑(finrank (ZMod q) G - finrank (ZMod q) V.direction) ≤
            2 ^ 171 * α.curlog ^ 4 * γ.curlog ^ 4 / ε ^ 24 ∧
          (1 + ε / 32) * α ≤ ‖𝟭_[ℝ] A * μ V'‖_[⊤] :=
  by
  obtain rfl | hA := A.eq_empty_or_nonempty
  stop
    refine' ⟨⊤, univ, _⟩
    rw [AffineSubspace.direction_top]
    simp only [AffineSubspace.top_coe, coe_univ, eq_self_iff_true, finrank_top, tsub_self,
      Nat.cast_zero, indicate_empty, MulZeroClass.zero_mul, lpnorm_zero, true_and_iff,
      Finset.card_empty, zero_div] at hαA ⊢
    exact ⟨by positivity, mul_nonpos_of_nonneg_of_nonpos (by positivity) hαA⟩
  have hγ₁ : γ ≤ 1 := hγC.trans (div_le_one_of_le (Nat.cast_le.2 C.card_le_univ) <| by positivity)
  have hG : (card G : ℝ) ≠ 0 := by positivity
  have :=
    unbalancing _ (mul_ne_zero two_ne_zero (Nat.ceil_pos.2 <| curlog_pos hγ hγ₁).ne') (ε / 2)
      (by positivity) (div_le_one_of_le (hε₁.le.trans <| by norm_num) <| by norm_num)
      (const _ (card G)⁻¹) (card G • (balance (μ A) ○ balance (μ A)))
      (sqrt (card G) • balance (μ A)) (const _ (card G)⁻¹) _ _ _ _
  rotate_left
  stop
    ext a : 1
    simp [smul_dconv, dconv_smul, smul_smul]
  · simp [card_univ, show (card G : ℂ) ≠ 0 by sorry]
  · simp only [comp_const, Nonneg.coe_inv, NNReal.coe_nat_cast]
    rw [← ENNReal.coe_one, lpnorm_const one_ne_zero]
    simp only [Nonneg.coe_one, inv_one, rpow_one, norm_inv, norm_coe_nat,
      mul_inv_cancel (show (card G : ℝ) ≠ 0 by positivity)]
  · have hγ' : (1 : ℝ≥0) ≤ 2 * ⌈γ.curlog⌉₊ := sorry
    simpa [wLpnorm_nsmul hγ', ← nsmul_eq_mul, div_le_iff' (show (0 : ℝ) < card G by positivity), ←
      div_div, *] using global_dichotomy hA hγC hγ hAC
  sorry

