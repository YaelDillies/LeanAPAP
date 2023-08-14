import data.complex.exponential_bounds
import prereqs.convolution.norm
import prereqs.misc

/-!
# Finite field case
-/

open finset fintype function real
open_locale nnreal

variables {G : Type*} [add_comm_group G] [decidable_eq G] [fintype G] {A C : finset G} {γ ε : ℝ}

lemma global_dichotomy (hA : A.nonempty) (hγC : γ ≤ C.card / card G) (hγ : 0 < γ)
  (hAC : ε ≤ |card G * ⟪μ A ∗ μ A, μ C⟫_[ℝ] - 1|) :
  ε / (2 * card G) ≤ ‖balance (μ_[ℝ] A) ○ balance (μ A)‖_[2 * ⌈γ.curlog⌉₊, const _ (card G)⁻¹] :=
begin
  have hC : C.nonempty,
  { rw nonempty_iff_ne_empty,
    rintro rfl,
    simpa [hγ.not_le] using hγC },
  have hγ₁ : γ ≤ 1 := hγC.trans (div_le_one_of_le (nat.cast_le.2 C.card_le_univ) $ by positivity),
  set p := 2 * ⌈γ.curlog⌉₊,
  have hp : 1 < p := nat.succ_le_iff.1
    (le_mul_of_one_le_right zero_le' $ nat.ceil_pos.2 $ curlog_pos hγ hγ₁),
  have hp' : (p⁻¹ : ℝ≥0) < 1 := inv_lt_one (by exact_mod_cast hp),
  rw [mul_comm, ←div_div, div_le_iff (zero_lt_two' ℝ)],
  calc
      _ ≤ _ : div_le_div_of_le (card G).cast_nonneg hAC
    ... = |⟪balance (μ A) ∗ balance (μ A), μ C⟫_[ℝ]| : _
    ... ≤ ‖balance (μ_[ℝ] A) ∗ balance (μ A)‖_[p] * ‖μ_[ℝ] C‖_[↑(1 - p⁻¹ : ℝ≥0)⁻¹]
        : abs_L2inner_le_Lpnorm_mul_Lpnorm ⟨by exact_mod_cast hp, _⟩ _ _
    ... ≤ ‖balance (μ_[ℝ] A) ○ balance (μ A)‖_[p] * (card G ^ (-p⁻¹ : ℝ) * γ ^ (-p⁻¹ : ℝ))
        : mul_le_mul (Lpnorm_conv_le_Lpnorm_dconv $ even_two_mul _) _ (by positivity)
            (by positivity)
    ... = ‖balance (μ_[ℝ] A) ○ balance (μ A)‖_[2 * ⌈γ.curlog⌉₊, const _ (card G)⁻¹] * γ ^ (-p⁻¹ : ℝ)
        : _
    ... ≤ _ : mul_le_mul_of_nonneg_left _ $ by positivity,
  { rw [←balance_conv, balance, L2inner_sub_left, L2inner_const_left, expect_conv, sum_mu ℝ hA,
      expect_mu ℝ hA, sum_mu ℝ hC, conj_trivial, one_mul, mul_one, ←mul_inv_cancel, ←mul_sub,
      abs_mul, abs_of_nonneg, mul_div_cancel_left];
    positivity },
  { rw [nnreal.coe_inv, nnreal.coe_sub hp'.le],
    simp },
  { rw [Lpnorm_mu (one_le_inv (tsub_pos_of_lt hp') tsub_le_self) hC, nnreal.coe_inv,
      nnreal.coe_sub hp'.le, nnreal.coe_one, inv_inv, sub_sub_cancel_left, ←mul_rpow],
    rw [le_div_iff, mul_comm] at hγC,
    refine rpow_le_rpow_of_nonpos _ hγC (neg_nonpos.2 _),
    all_goals { positivity } },
  { simp_rw [nat.cast_mul, nat.cast_two],
    rw [wLpnorm_const, mul_assoc, mul_left_comm, nnreal.coe_inv, inv_rpow, rpow_neg],
    push_cast,
    all_goals { positivity } },
  { push_cast,
    norm_num,
    rw [←neg_mul, rpow_mul, one_div, rpow_inv_le_iff_of_pos],
    refine (rpow_le_rpow_of_exponent_ge hγ hγ₁ $ neg_le_neg $ inv_le_inv_of_le (curlog_pos hγ hγ₁) $
      nat.le_ceil _).trans ((rpow_neg_inv_curlog hγ.le hγ₁).trans $ exp_one_lt_d9.le.trans $
      by norm_num),
    all_goals { positivity } }
end
