import Mathlib.FieldTheory.Finite.Basic
import LeanAPAP.Mathlib.Combinatorics.Additive.FreimanHom
import LeanAPAP.Mathlib.Data.Finset.Pointwise.Basic
import LeanAPAP.Prereqs.Convolution.ThreeAP
import LeanAPAP.Prereqs.LargeSpec
import LeanAPAP.Physics.AlmostPeriodicity
import LeanAPAP.Physics.Unbalancing

/-!
# Finite field case
-/

attribute [-simp] div_pow

open FiniteDimensional Fintype Function Real MeasureTheory
open Finset hiding card
open scoped NNReal BigOperators Combinatorics.Additive Pointwise

universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G] [Fintype G] [MeasurableSpace G]
  [DiscreteMeasurableSpace G] {A C : Finset G} {γ ε : ℝ}

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
  rw [mul_comm, ← div_div, div_le_iff₀ (zero_lt_two' ℝ)]
  calc
    _ ≤ _ := div_le_div_of_nonneg_right hAC (card G).cast_nonneg
    _ = |⟪balance (μ A) ∗ balance (μ A), μ C⟫_[ℝ]| := ?_
    _ ≤ ‖balance (μ_[ℝ] A) ∗ balance (μ A)‖_[p] * ‖μ_[ℝ] C‖_[NNReal.conjExponent p] :=
        abs_dL2Inner_le_dLpNorm_mul_dLpNorm hp'' _ _
    _ ≤ ‖balance (μ_[ℝ] A) ○ balance (μ A)‖_[p] * (card G ^ (-(p : ℝ)⁻¹) * γ ^ (-(p : ℝ)⁻¹)) :=
        mul_le_mul (dLpNorm_conv_le_dLpNorm_dconv' (by positivity) (even_two_mul _) _) ?_
          (by positivity) (by positivity)
    _ = ‖balance (μ_[ℝ] A) ○ balance (μ A)‖_[↑(2 * ⌈γ.curlog⌉₊), const _ (card G)⁻¹] *
          γ ^ (-(p : ℝ)⁻¹) := ?_
    _ ≤ _ := mul_le_mul_of_nonneg_left ?_ $ by positivity
  · rw [← balance_conv, balance, dL2Inner_sub_left, dL2Inner_const_left, expect_conv, sum_mu ℝ hA,
      expect_mu ℝ hA, sum_mu ℝ hC, conj_trivial, one_mul, mul_one, ← mul_inv_cancel₀, ← mul_sub,
      abs_mul, abs_of_nonneg, mul_div_cancel_left₀] <;> positivity
  · rw [dLpNorm_mu hp''.symm.one_le hC, hp''.symm.coe.inv_sub_one, NNReal.coe_natCast, ← mul_rpow]
    rw [nnratCast_dens, le_div_iff₀, mul_comm] at hγC
    refine rpow_le_rpow_of_nonpos ?_ hγC (neg_nonpos.2 ?_)
    all_goals positivity
  · rw [mul_comm, wLpNorm_const_right, mul_right_comm, rpow_neg, ← inv_rpow]
    congr
    any_goals positivity
    exact ENNReal.natCast_ne_top _
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
        -- rw [conv_assoc, conv_dL2Inner, ← conj_dL2Inner]
        -- simp

      _ = _ := sorry
  sorry

lemma di_in_ff (hq₃ : 3 ≤ q) (hq : q.Prime) (hε₀ : 0 < ε) (hε₁ : ε < 1) (hαA : α ≤ A.dens)
    (hγC : γ ≤ C.dens) (hγ : 0 < γ) (hAC : ε ≤ |card G * ⟪μ A ∗ μ A, μ C⟫_[ℝ] - 1|) :
    ∃ (V : Submodule (ZMod q) G) (_ : DecidablePred (· ∈ V)),
        ↑(finrank (ZMod q) G - finrank (ZMod q) V) ≤
            2 ^ 171 * α.curlog ^ 4 * γ.curlog ^ 4 / ε ^ 24 ∧
          (1 + ε / 32) * α ≤ ‖𝟭_[ℝ] A ∗ μ (Set.toFinset V)‖_[⊤] := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · stop
    refine ⟨⊤, univ, _⟩
    rw [AffineSubspace.direction_top]
    simp only [AffineSubspace.top_coe, coe_univ, eq_self_iff_true, finrank_top, tsub_self,
      Nat.cast_zero, indicate_empty, zero_mul, nnLpNorm_zero, true_and_iff,
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
    unfold const
    rw [dLpNorm_const one_ne_zero]
    sorry
    -- simp only [Nonneg.coe_one, inv_one, rpow_one, norm_inv, norm_coe_nat,
    --   mul_inv_cancel₀ (show (card G : ℝ) ≠ 0 by positivity)]
  · have hγ' : (1 : ℝ≥0) ≤ 2 * ⌈γ.curlog⌉₊ := sorry
    sorry
    -- simpa [wLpNorm_nsmul hγ', ← nsmul_eq_mul, div_le_iff' (show (0 : ℝ) < card G by positivity),
    --   ← div_div, *] using global_dichotomy hA hγC hγ hAC
  sorry

theorem ff (hq₃ : 3 ≤ q) (hq : q.Prime) {A : Finset G} (hA₀ : A.Nonempty)
    (hA : ThreeAPFree (α := G) A) : finrank (ZMod q) G ≤ 2 ^ 203 * curlog A.dens ^ 9 := by
  let n : ℝ := finrank (ZMod q) G
  let α : ℝ := A.dens
  have : 1 < (q : ℝ) := mod_cast hq₃.trans_lt' (by norm_num)
  have : 1 ≤ (q : ℝ) := this.le
  have : NeZero q := ⟨by positivity⟩
  have : Fact q.Prime := ⟨hq⟩
  have hq' : Odd q := hq.odd_of_ne_two $ by rintro rfl; simp at hq₃
  have : 1 ≤ α⁻¹ := one_le_inv (by positivity) (by simp [α])
  have hα₀ : 0 < α := by positivity
  have : 0 ≤ log α⁻¹ := log_nonneg ‹_›
  have : 0 ≤ curlog α := curlog_nonneg (by positivity) (by simp [α])
  have : 0 < log q := log_pos ‹_›
  obtain hα | hα := le_total (q ^ (n / 2) : ℝ) (2 * α⁻¹ ^ 2)
  · rw [rpow_le_iff_le_log, log_mul, log_pow, Nat.cast_two, ← mul_div_right_comm,
      mul_div_assoc, ← le_div_iff₀] at hα
    calc
      _ ≤ (log 2 + 2 * log α⁻¹) / (log q / 2) := hα
      _ = 4 / log q * (log α⁻¹ + log 2 / 2) := by ring
      _ ≤ 2 ^ 203 * (0 + 2) ^ 8 * (log α⁻¹ + 2) := by
        gcongr
        · calc
            4 / log q ≤ 4 / log 3 := by gcongr; assumption_mod_cast
            _ ≤ 4 / log 2 := by gcongr; norm_num
            _ ≤ 4 / 0.6931471803 := by gcongr; exact log_two_gt_d9.le
            _ ≤ 2 ^ 203 * (0 + 2) ^ 8 := by norm_num
        · calc
            log 2 / 2 ≤ 0.6931471808 / 2 := by gcongr; exact log_two_lt_d9.le
            _ ≤ 2 := by norm_num
      _ ≤ 2 ^ 203 * (log α⁻¹ + 2) ^ 8 * (log α⁻¹ + 2) := by gcongr
      _ = 2 ^ 203 * curlog α ^ 9 := by
        rw [curlog_eq_log_inv_add_two, pow_succ _ 8, mul_assoc]; positivity
    all_goals positivity
  have ind (i : ℕ) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Fintype V) (_ : DecidableEq V) (_ : Module (ZMod q) V)
      (B : Finset V), n ≤ finrank (ZMod q) V + 2 ^ 195 * i * curlog α ^ 8 ∧ ThreeAPFree (B : Set V)
        ∧ α ≤ B.dens ∧
      (B.dens < (65 / 64 : ℝ) ^ i * α →
        2⁻¹ ≤ card V * ⟪μ B ∗ μ B, μ (B.image (2 • ·))⟫_[ℝ]) := by
    induction' i with i ih hi
    · exact ⟨G, inferInstance, inferInstance, inferInstance, inferInstance, A, by simp, hA,
        by simp, by simp [α, nnratCast_dens, Fintype.card_subtype, subset_iff]⟩
    obtain ⟨V, _, _, _, _, B, hV, hB, hαβ, hBV⟩ := ih
    obtain hB' | hB' := le_or_lt 2⁻¹ (card V * ⟪μ B ∗ μ B, μ (B.image (2 • ·))⟫_[ℝ])
    · exact ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, B,
        hV.trans (by gcongr; exact i.le_succ), hB, hαβ, fun _ ↦ hB'⟩
    let _ : MeasurableSpace V := ⊤
    have : DiscreteMeasurableSpace V := ⟨fun _ ↦ trivial⟩
    have : 0 ≤ curlog B.dens := curlog_nonneg (by positivity) (by simp)
    have : 2⁻¹ ≤ |card V * ⟪μ B ∗ μ B, μ (B.image (2 • ·))⟫_[ℝ] - 1| := by
      rw [abs_sub_comm, le_abs, le_sub_comm]
      norm_num at hB' ⊢
      exact .inl hB'.le
    obtain ⟨V', _, hVV', hv'⟩ := di_in_ff hq₃ hq (by positivity) two_inv_lt_one le_rfl (by
      rwa [Finset.dens_image (Nat.Coprime.nsmul_right_bijective _)]
      simpa [card_eq_pow_finrank (K := ZMod q) (V := V), ZMod.card] using hq'.pow) hα₀ this
    rw [dLinftyNorm_eq_iSup_norm, ← Finset.sup'_univ_eq_ciSup, Finset.le_sup'_iff] at hv'
    obtain ⟨x, -, hx⟩ := hv'
    let B' : Finset V' := (-x +ᵥ B).preimage (↑) Set.injOn_subtype_val
    have hβ : (1 + 64⁻¹ : ℝ) * B.dens ≤ B'.dens := sorry
    simp at hx
    refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, B', ?_, ?_, ?_,
      fun h ↦ ?_⟩
    · calc
        n ≤ finrank (ZMod q) V + 2 ^ 195 * i * curlog α ^ 8 := hV
        _ ≤ finrank (ZMod q) V' + ↑(finrank (ZMod q) V - finrank (ZMod q) V') +
            2 ^ 195 * i * curlog α ^ 8 := by gcongr; norm_cast; exact le_add_tsub
        _ ≤ finrank (ZMod q) V' + 2 ^ 171 * curlog B.dens ^ 4 * curlog α ^ 4 / 2⁻¹ ^ 24 +
            2 ^ 195 * i * curlog α ^ 8 := by gcongr
        _ ≤ finrank (ZMod q) V' + 2 ^ 171 * curlog α ^ 4 * curlog α ^ 4 / 2⁻¹ ^ 24 +
            2 ^ 195 * i * curlog α ^ 8 := by gcongr; sorry
        _ = _ := by push_cast; ring
    · exact .of_image .subtypeVal Set.injOn_subtype_val (Set.subset_univ _)
        (hB.vadd_set (a := -x) |>.mono $ by simp [B'])
    · calc
        α ≤ B.dens := hαβ
        _ ≤ (1 + 64⁻¹) * B.dens := by simp [one_add_mul]; positivity
        _ ≤ B'.dens := hβ
    · refine (h.not_le $ ?_).elim
      calc
        (65 / 64) ^ (i + 1) * α = (1 + 64⁻¹) * ((65 / 64) ^ i * α) := by ring
        _ ≤ (1 + 64⁻¹) * B.dens := by gcongr; simpa [hB'.not_le] using hBV
        _ ≤ B'.dens := hβ
  obtain ⟨V, _, _, _, _, B, hV, hB, hαβ, hBV⟩ := ind ⌊curlog α / log (65 / 64)⌋₊
  let β : ℝ := B.dens
  have aux : 0 < log (65 / 64) := log_pos (by norm_num)
  specialize hBV $ by
    calc
      _ ≤ (1 : ℝ) := mod_cast dens_le_one
      _ < _ := ?_
    rw [← inv_pos_lt_iff_one_lt_mul, lt_pow_iff_log_lt, ← div_lt_iff]
    calc
      log α⁻¹ / log (65 / 64)
        < ⌊log α⁻¹ / log (65 / 64)⌋₊ + 1 := Nat.lt_floor_add_one _
      _ = ⌊(log α⁻¹ + log (65 / 64)) / log (65 / 64)⌋₊ := by
        rw [← div_add_one aux.ne', Nat.floor_add_one, Nat.cast_succ]
        exact div_nonneg (log_nonneg $ one_le_inv (by positivity) (by simp [α])) aux.le
      _ ≤ ⌊curlog α / log (65 / 64)⌋₊ := by
        rw [curlog_eq_log_inv_add_two]
        gcongr
        · calc
            log (65 / 64) ≤ 65/64 - 1 := log_le_sub_one_of_pos $ by norm_num
            _ ≤ 2 := by norm_num
        · positivity
    all_goals positivity
  rw [hB.dL2Inner_mu_conv_mu_mu_two_smul_mu] at hBV
  suffices h : (q ^ (n - 2 ^ 202 * curlog α ^ 9) : ℝ) ≤ q ^ (n / 2) by
    rwa [rpow_le_rpow_left_iff ‹_›, sub_le_comm, sub_half, div_le_iff₀' zero_lt_two, ← mul_assoc,
      ← pow_succ'] at h
  calc
    _ ≤ ↑q ^ (finrank (ZMod q) V : ℝ) := by
      gcongr
      · assumption
      rw [sub_le_comm]
      calc
        n - finrank (ZMod q) V ≤ 2 ^ 195 * ⌊curlog α / log (65 / 64)⌋₊ * curlog α ^ 8 := by
          rwa [sub_le_iff_le_add']
        _ ≤ 2 ^ 195 * (curlog α / log (65 / 64)) * curlog α ^ 8 := by
          gcongr; exact Nat.floor_le (by positivity)
        _ = 2 ^ 195 * (log (65 / 64)) ⁻¹ * curlog α ^ 9 := by ring
        _ ≤ 2 ^ 195 * 2 ^ 7 * curlog α ^ 9 := by
          gcongr
          rw [inv_le ‹_› (by positivity)]
          calc
            (2 ^ 7)⁻¹ ≤ 1 - (65 / 64)⁻¹ := by norm_num
            _ ≤ log (65 / 64) := one_sub_inv_le_log_of_pos (by positivity)
        _ = 2 ^ 202 * curlog α ^ 9  := by ring
    _ = ↑(card V) := by simp [card_eq_pow_finrank (K := ZMod q) (V := V)]
    _ ≤ 2 * β⁻¹ ^ 2 := by
      rw [← natCast_card_mul_nnratCast_dens, mul_pow, mul_inv, ← mul_assoc,
        ← div_eq_mul_inv (card V : ℝ), ← zpow_one_sub_natCast₀ (by positivity)] at hBV
      have : 0 < (card V : ℝ) := by positivity
      simpa [le_inv_mul_iff₀, mul_inv_le_iff₀, this, zero_lt_two, mul_comm] using hBV
    _ ≤ 2 * α⁻¹ ^ 2 := by gcongr
    _ ≤ _ := hα
  simpa [card_eq_pow_finrank (K := ZMod q) (V := V), ZMod.card] using hq'.pow
