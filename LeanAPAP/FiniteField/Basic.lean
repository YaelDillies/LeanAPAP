import Mathlib.FieldTheory.Finite.Basic
import LeanAPAP.Mathlib.Combinatorics.Additive.FreimanHom
import LeanAPAP.Mathlib.Data.Finset.Preimage
import LeanAPAP.Prereqs.Convolution.ThreeAP
import LeanAPAP.Prereqs.LargeSpec
import LeanAPAP.Physics.AlmostPeriodicity
import LeanAPAP.Physics.DRC
import LeanAPAP.Physics.Unbalancing
import LeanAPAP.Prereqs.Function.Indicator.Complex

/-!
# Finite field case
-/

attribute [-simp] div_pow Real.log_inv

open FiniteDimensional Fintype Function Real MeasureTheory
open Finset hiding card
open scoped NNReal BigOperators Combinatorics.Additive Pointwise

universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G] [Fintype G] {A C : Finset G} {x y γ ε : ℝ}

local notation "𝓛" x:arg => 1 + log x⁻¹

private lemma curlog_pos (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : 0 < 𝓛 x := by
  obtain rfl | hx₀ := hx₀.eq_or_lt
  · simp
  have : 0 ≤ log x⁻¹ := log_nonneg $ one_le_inv (by positivity) hx₁
  positivity

private lemma rpow_inv_neg_curlog_le (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : x⁻¹ ^ (𝓛 x)⁻¹ ≤ exp 1 := by
  obtain rfl | hx₀ := hx₀.eq_or_lt
  · simp; positivity
  obtain rfl | hx₁ := hx₁.eq_or_lt
  · simp
  have hx := one_lt_inv hx₀ hx₁
  calc
    x⁻¹ ^ (𝓛 x)⁻¹ ≤ x⁻¹ ^ (log x⁻¹)⁻¹ := by
      gcongr
      · exact hx.le
      · exact log_pos hx
      · simp
    _ ≤ exp 1 := x⁻¹.rpow_inv_log_le_exp_one

private lemma curlog_mul_le (hx₀ : 0 < x) (hx₁ : x ≤ 1) (hy₀ : 0 < y) (hy₁ : y ≤ 1) :
    𝓛 (x * y) ≤ x⁻¹ * 𝓛 y := by
  suffices h : log x⁻¹ - (x⁻¹ - 1) ≤ (x⁻¹ - 1) * log y⁻¹ by
    rw [← sub_nonneg] at h ⊢
    exact h.trans_eq (by rw [mul_inv, log_mul]; ring; all_goals positivity)
  calc
    log x⁻¹ - (x⁻¹ - 1) ≤ 0 := sub_nonpos.2 $ log_le_sub_one_of_pos $ by positivity
    _ ≤ (x⁻¹ - 1) * log y⁻¹ :=
      mul_nonneg (sub_nonneg.2 $ one_le_inv hx₀ hx₁) $ log_nonneg $ one_le_inv hy₀ hy₁

private lemma curlog_rpow_le' (hx₀ : 0 < x) (hx₁ : x ≤ 1) (hy₀ : 0 < y) (hy₁ : y ≤ 1) :
    𝓛 (x ^ y) ≤ y⁻¹ * 𝓛 x := by
  suffices h : 1 - y⁻¹ ≤ (y⁻¹ - y) * log x⁻¹ by
    rw [← sub_nonneg] at h ⊢
    exact h.trans_eq (by rw [← inv_rpow, log_rpow]; ring; all_goals positivity)
  calc
    1 - y⁻¹ ≤ 0 := sub_nonpos.2 $ one_le_inv hy₀ hy₁
    _ ≤ (y⁻¹ - y) * log x⁻¹ :=
      mul_nonneg (sub_nonneg.2 $ hy₁.trans $ one_le_inv hy₀ hy₁) $ log_nonneg $ one_le_inv hx₀ hx₁

private lemma curlog_rpow_le (hx₀ : 0 < x) (hy : 1 ≤ y) : 𝓛 (x ^ y) ≤ y * 𝓛 x := by
  rw [← inv_rpow, log_rpow, mul_one_add]
  gcongr
  all_goals positivity

private lemma curlog_pow_le {n : ℕ} (hx₀ : 0 < x) (hn : n ≠ 0) : 𝓛 (x ^ n) ≤ n * 𝓛 x := by
  rw [← rpow_natCast]; exact curlog_rpow_le hx₀ $ mod_cast Nat.one_le_iff_ne_zero.2 hn

lemma global_dichotomy [MeasurableSpace G] [DiscreteMeasurableSpace G] (hA : A.Nonempty)
    (hγC : γ ≤ C.dens) (hγ : 0 < γ) (hAC : ε ≤ |card G * ⟪μ A ∗ μ A, μ C⟫_[ℝ] - 1|) :
    ε / (2 * card G) ≤ ‖balance (μ_[ℝ] A) ○ balance (μ A)‖_[↑(2 * ⌈𝓛 γ⌉₊), const _ (card G)⁻¹] := by
  have hC : C.Nonempty := by simpa using hγ.trans_le hγC
  have hγ₁ : γ ≤ 1 := hγC.trans (by norm_cast; exact dens_le_one)
  set p := 2 * ⌈𝓛 γ⌉₊
  have hp : 1 < p :=
    Nat.succ_le_iff.1 (le_mul_of_one_le_right zero_le' $ Nat.ceil_pos.2 $ curlog_pos hγ.le hγ₁)
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
    _ = ‖balance (μ_[ℝ] A) ○ balance (μ A)‖_[↑(2 * ⌈𝓛 γ⌉₊), const _ (card G)⁻¹] *
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
  · have : 1 ≤ γ⁻¹ := one_le_inv hγ hγ₁
    have : 0 ≤ log γ⁻¹ := log_nonneg this
    calc
      γ ^ (-(↑p)⁻¹ : ℝ) = √(γ⁻¹ ^ ((↑⌈1 + log γ⁻¹⌉₊)⁻¹ : ℝ)) := by
        rw [rpow_neg hγ.le, inv_rpow hγ.le]
        unfold_let p
        push_cast
        rw [mul_inv_rev, rpow_mul, sqrt_eq_rpow, one_div, inv_rpow] <;> positivity
      _ ≤ √(γ⁻¹ ^ ((1 + log γ⁻¹)⁻¹ : ℝ)) := by gcongr; assumption; exact Nat.le_ceil _
      _ ≤ √ (exp 1) := by gcongr; exact rpow_inv_neg_curlog_le hγ.le hγ₁
      _ ≤ √ 2.7182818286 := by gcongr; exact exp_one_lt_d9.le
      _ ≤ 2 := by rw [sqrt_le_iff]; norm_num

variable {q n : ℕ} [Module (ZMod q) G] {A₁ A₂ : Finset G} (S : Finset G) {α : ℝ}

lemma ap_in_ff (hα₀ : 0 < α) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hαA₁ : α ≤ A₁.dens)
    (hαA₂ : α ≤ A₂.dens) :
    ∃ (V : Submodule (ZMod q) G) (_ : DecidablePred (· ∈ V)),
        ↑(finrank (ZMod q) G - finrank (ZMod q) V) ≤
            2 ^ 27 * 𝓛 α ^ 2 * 𝓛 (ε * α) ^ 2 / ε ^ 2 ∧
          |∑ x ∈ S, (μ (Set.toFinset V) ∗ μ A₁ ∗ μ A₂) x - ∑ x ∈ S, (μ A₁ ∗ μ A₂) x| ≤ ε := by
  classical
  let _ : MeasurableSpace G := ⊤
  have : DiscreteMeasurableSpace G := ⟨fun _ ↦ trivial⟩
  have hA₁ : A₁.Nonempty := by simpa using hα₀.trans_le hαA₁
  have hA₂ : A₂.Nonempty := by simpa using hα₀.trans_le hαA₂
  have hα₁ : α ≤ 1 := hαA₁.trans $ mod_cast A₁.dens_le_one
  have : 0 ≤ log α⁻¹ := log_nonneg $ one_le_inv hα₀ hα₁
  have : 0 ≤ log (ε * α)⁻¹ := log_nonneg $ one_le_inv (by positivity) $ mul_le_one hε₁ hα₀.le hα₁
  obtain rfl | hS := S.eq_empty_or_nonempty
  · exact ⟨⊤, inferInstance, by simp [hε₀.le]; positivity⟩
  have hA₁ : σ[A₁, univ] ≤ α⁻¹ :=
    calc
      _ ≤ (A₁.dens⁻¹ : ℝ) := by norm_cast; exact addConst_le_inv_dens
      _ ≤ α⁻¹ := by gcongr
  obtain ⟨T, hST, hT⟩ := AlmostPeriodicity.linfty_almost_periodicity_boosted ε hε₀ hε₁
    ⌈𝓛 (ε * α / 4)⌉₊ (Nat.ceil_pos.2 $ curlog_pos (by positivity) sorry).ne' sorry hA₁
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

lemma di_in_ff [MeasurableSpace G] [DiscreteMeasurableSpace G] (hq₃ : 3 ≤ q) (hq : q.Prime)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (hA₀ : A.Nonempty)
    (hγC : γ ≤ C.dens) (hγ : 0 < γ) (hAC : ε ≤ |card G * ⟪μ A ∗ μ A, μ C⟫_[ℝ] - 1|) :
    ∃ (V : Submodule (ZMod q) G) (_ : DecidablePred (· ∈ V)),
        ↑(finrank (ZMod q) G - finrank (ZMod q) V) ≤
            2 ^ 179 * 𝓛 A.dens ^ 4 * 𝓛 γ ^ 4 / ε ^ 24 ∧
          (1 + ε / 32) * A.dens ≤ ‖𝟭_[ℝ] A ∗ μ (Set.toFinset V)‖_[⊤] := by
  have hγ₁ : γ ≤ 1 := hγC.trans (by norm_cast; exact dens_le_one)
  have hG : (card G : ℝ) ≠ 0 := by positivity
  let α : ℝ := A.dens
  let p : ℕ := 2 * ⌈𝓛 γ⌉₊
  let p' : ℝ := 240 / ε * log (6 / ε) * p
  let q' : ℕ := 2 * ⌈p' + 2 ^ 8 * ε⁻¹ ^ 2 * log (64 / ε)⌉₊
  let f : G → ℝ := balance (μ A)
  have hα₀ : 0 < α := by positivity
  have hα₁ : α ≤ 1 := by unfold_let α; exact mod_cast A.dens_le_one
  have : 0 < 𝓛 γ := curlog_pos hγ.le hγ₁
  have : 0 < p := by positivity
  have : 0 < log (6 / ε) := log_pos $ (one_lt_div hε₀).2 (by linarith)
  have : 0 < p' := by positivity
  have : 0 < log (64 / ε) := log_pos $ (one_lt_div hε₀).2 (by linarith)
  have : 0 < q' := by positivity
  have : q' ≤ 2 ^ 30 * 𝓛 γ / ε ^ 5 := sorry
  have :=
    calc
      1 + ε / 4 = 1 + ε / 2 / 2 := by ring
      _ ≤ _ := by
        refine unbalancing _ (mul_ne_zero two_ne_zero (Nat.ceil_pos.2 $ curlog_pos hγ.le hγ₁).ne')
          (ε / 2) (by positivity) (div_le_one_of_le (hε₁.le.trans $ by norm_num) $ by norm_num)
          (card G • (balance (μ A) ○ balance (μ A))) (sqrt (card G) • balance (μ A))
          (const _ (card G)⁻¹) ?_ ?_ ?_
        · ext a : 1
          simp [smul_dconv, dconv_smul, smul_smul, ← mul_assoc, ← sq, ← Complex.ofReal_pow]
        · simp [card_univ, show (card G : ℂ) ≠ 0 by sorry]
        · have hγ' : (1 : ℝ≥0) ≤ 2 * ⌈𝓛 γ⌉₊ := sorry
          sorry
          -- simpa [wLpNorm_nsmul hγ', ← nsmul_eq_mul, div_le_iff' (show (0 : ℝ) < card G by positivity),
          --   ← div_div, *] using global_dichotomy hA hγC hγ hAC
      _ = card G ^ (-(↑p')⁻¹ : ℝ) * ‖card G • (f ○ f) + 1‖_[.ofReal p'] := by
        congr 3 <;> ring_nf; simp [hε₀.ne']; ring
  obtain ⟨A₁, A₂, hA, hA₁, hA₂⟩ : ∃ (A₁ A₂ : Finset G),
      1 - ε / 32 ≤ ∑ x ∈ s q' (ε / 16) univ univ A, (μ A₁ ○ μ A₂) x ∧
        (4⁻¹ : ℝ) * A.dens ^ (2 * q') ≤ A₁.dens ∧ (4⁻¹ : ℝ) * A.dens ^ (2 * q') ≤ A₂.dens :=
    sifting_cor (ε := ε / 16) (δ := ε / 32) (by positivity) (by linarith) (by positivity) (p := q')
    (even_two_mul _) (le_mul_of_one_le_right zero_le_two (by simp; positivity)) (by
      calc
        (ε / 16)⁻¹ * log (2 / (ε / 32)) = 2 ^ 4 * ε⁻¹ ^ 1 * log (64 / ε) := by ring_nf
        _ ≤ 2 ^ 8 * ε⁻¹ ^ 2 * log (64 / ε) := by
          gcongr
          · norm_num
          · norm_num
          · exact one_le_inv hε₀ hε₁.le
          · norm_num
        _ ≤ ⌈2 ^ 8 * ε⁻¹ ^ 2 * log (64 / ε)⌉₊ := Nat.le_ceil _
        _ = ↑(1 * ⌈0 + 2 ^ 8 * ε⁻¹ ^ 2 * log (64 / ε)⌉₊) := by rw [one_mul, zero_add]
        _ ≤ q' := by unfold_let q'; gcongr; norm_num) hA₀
  let s' : Finset G := {x | 1 + ε / 8 ≤ card G • (μ A ○ μ A) x}
  have hss' : s q' (ε / 16) univ univ A ⊆ s' := sorry
  obtain ⟨V, _, hVdim, hV⟩ : ∃ (V : Submodule (ZMod q) G) (_ : DecidablePred (· ∈ V)),
    ↑(finrank (ZMod q) G - finrank (ZMod q) V) ≤
        2 ^ 27 * 𝓛 (4⁻¹ * α ^ (2 * q')) ^ 2 * 𝓛 (ε / 32 * (4⁻¹ * α ^ (2 * q'))) ^ 2 / (ε / 32) ^ 2 ∧
      |∑ x ∈ s', (μ (Set.toFinset V) ∗ μ A₁ ∗ μ A₂) x - ∑ x ∈ s', (μ A₁ ∗ μ A₂) x| ≤ ε / 32 :=
    ap_in_ff _ (by positivity) (by positivity) (by linarith) hA₁ hA₂
  refine ⟨V, inferInstance, ?_, ?_⟩
  · calc
      ↑(finrank (ZMod q) G - finrank (ZMod q) V)
        ≤ 2 ^ 27 * 𝓛 (4⁻¹ * α ^ (2 * q')) ^ 2 *
          𝓛 (ε / 32 * (4⁻¹ * α ^ (2 * q'))) ^ 2 / (ε / 32) ^ 2 := hVdim
      _ ≤ 2 ^ 27 * (8 * q' * 𝓛 α) ^ 2 *
          (2 ^ 8 * q' * 𝓛 α / ε) ^ 2 / (ε / 32) ^ 2 := by
        have : α ^ (2 * q') ≤ 1 := pow_le_one _ hα₀.le hα₁
        have : 4⁻¹ * α ^ (2 * q') ≤ 1 := mul_le_one (by norm_num) (by positivity) ‹_›
        have : ε / 32 * (4⁻¹ * α ^ (2 * q')) ≤ 1 := mul_le_one (by linarith) (by positivity) ‹_›
        have : 0 ≤ log (ε / 32 * (4⁻¹ * α ^ (2 * q')))⁻¹ :=
          log_nonneg $ one_le_inv (by positivity) ‹_›
        have : 0 ≤ log (4⁻¹ * α ^ (2 * q'))⁻¹ := log_nonneg $ one_le_inv (by positivity) ‹_›
        have : 0 ≤ log (α ^ (2 * q'))⁻¹ := log_nonneg $ one_le_inv (by positivity) ‹_›
        have :=
          calc
            𝓛 (4⁻¹ * α ^ (2 * q')) ≤ 4⁻¹⁻¹ * 𝓛 (α ^ (2 * q')) :=
              curlog_mul_le (by norm_num) (by norm_num) (by positivity) ‹_›
            _ ≤ 4⁻¹⁻¹ * (↑(2 * q') *  𝓛 α) := by gcongr; exact curlog_pow_le hα₀ (by positivity)
            _ = 8 * q' * 𝓛 α := by push_cast; ring
        gcongr
        calc
          𝓛 (ε / 32 * (4⁻¹ * α ^ (2 * q'))) ≤ (ε / 32)⁻¹ * 𝓛 (4⁻¹ * (α ^ (2 * q'))) :=
            curlog_mul_le (by positivity) (by linarith) (by positivity) ‹_›
          _ ≤ (ε / 32)⁻¹ * (8 * q' * 𝓛 α) := by gcongr
          _ = 2 ^ 8 * q' * 𝓛 α / ε := by ring
      _ = 2 ^ 59 * q' ^ 4 * 𝓛 α ^ 4 / ε ^ 4 := by ring
      _ ≤ 2 ^ 59 * (2 ^ 30 * 𝓛 γ / ε ^ 5) ^ 4 * 𝓛 α ^ 4 / ε ^ 4 := by gcongr
      _ = 2 ^ 179 * 𝓛 α ^ 4 * 𝓛 γ ^ 4 / ε ^ 24 := by ring
  · sorry

theorem ff (hq₃ : 3 ≤ q) (hq : q.Prime) {A : Finset G} (hA₀ : A.Nonempty)
    (hA : ThreeAPFree (α := G) A) : finrank (ZMod q) G ≤ 2 ^ 211 * 𝓛 A.dens ^ 9 := by
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
  have : 0 < 𝓛 α := by positivity
  have : 0 < log q := log_pos ‹_›
  obtain hα | hα := le_total (q ^ (n / 2) : ℝ) (2 * α⁻¹ ^ 2)
  · rw [rpow_le_iff_le_log, log_mul, log_pow, Nat.cast_two, ← mul_div_right_comm,
      mul_div_assoc, ← le_div_iff₀] at hα
    calc
      _ ≤ (log 2 + 2 * log α⁻¹) / (log q / 2) := hα
      _ = 4 / log q * (log 2 / 2 + log α⁻¹) := by ring
      _ ≤ 2 ^ 211 * (1 + 0) ^ 8 * (1 + log α⁻¹) := by
        gcongr
        · calc
            4 / log q ≤ 4 / log 3 := by gcongr; assumption_mod_cast
            _ ≤ 4 / log 2 := by gcongr; norm_num
            _ ≤ 4 / 0.6931471803 := by gcongr; exact log_two_gt_d9.le
            _ ≤ 2 ^ 211 * (1 + 0) ^ 8 := by norm_num
        · calc
            log 2 / 2 ≤ 0.6931471808 / 2 := by gcongr; exact log_two_lt_d9.le
            _ ≤ 1 := by norm_num
      _ ≤ 2 ^ 211 * 𝓛 α ^ 8 * 𝓛 α := by gcongr
      _ = 2 ^ 211 * 𝓛 α ^ 9 := by rw [pow_succ _ 8, mul_assoc]
    all_goals positivity
  have ind (i : ℕ) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Fintype V) (_ : DecidableEq V) (_ : Module (ZMod q) V)
      (B : Finset V), n ≤ finrank (ZMod q) V + 2 ^ 203 * i * 𝓛 α ^ 8 ∧ ThreeAPFree (B : Set V)
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
    have : 0 < 𝓛 B.dens := curlog_pos (by positivity) (by simp)
    have : 2⁻¹ ≤ |card V * ⟪μ B ∗ μ B, μ (B.image (2 • ·))⟫_[ℝ] - 1| := by
      rw [abs_sub_comm, le_abs, le_sub_comm]
      norm_num at hB' ⊢
      exact .inl hB'.le
    obtain ⟨V', _, hVV', hv'⟩ := di_in_ff hq₃ hq (by positivity) two_inv_lt_one
      (by simpa using hα₀.trans_le hαβ) (by
      rwa [Finset.dens_image (Nat.Coprime.nsmul_right_bijective _)]
      simpa [card_eq_pow_finrank (K := ZMod q) (V := V), ZMod.card] using hq'.pow) hα₀ this
    rw [dLinftyNorm_eq_iSup_norm, ← Finset.sup'_univ_eq_ciSup, Finset.le_sup'_iff] at hv'
    obtain ⟨x, -, hx⟩ := hv'
    let B' : Finset V' := (-x +ᵥ B).preimage (↑) Set.injOn_subtype_val
    have hβ := by
      calc
        ((1 + 64⁻¹ : ℝ) * B.dens : ℝ) = (1 + 2⁻¹ / 32) * B.dens := by ring
        _ ≤ ‖(𝟭_[ℝ] B ∗ μ (V' : Set V).toFinset) x‖ := hx
        _ = B'.dens := ?_
      rw [mu, conv_smul, Pi.smul_apply, indicate_conv_indicate_eq_card_vadd_inter_neg,
        norm_of_nonneg (by positivity), nnratCast_dens, card_preimage, smul_eq_mul, inv_mul_eq_div]
      congr 2
      · congr 1 with x
        simp
      · simp
    simp at hx
    refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, B', ?_, ?_, ?_,
      fun h ↦ ?_⟩
    · calc
        n ≤ finrank (ZMod q) V + 2 ^ 203 * i * 𝓛 α ^ 8 := hV
        _ ≤ finrank (ZMod q) V' + ↑(finrank (ZMod q) V - finrank (ZMod q) V') +
            2 ^ 203 * i * 𝓛 α ^ 8 := by gcongr; norm_cast; exact le_add_tsub
        _ ≤ finrank (ZMod q) V' + 2 ^ 179 * 𝓛 B.dens ^ 4 * 𝓛 α ^ 4 / 2⁻¹ ^ 24 +
            2 ^ 203 * i * 𝓛 α ^ 8 := by gcongr
        _ ≤ finrank (ZMod q) V' + 2 ^ 179 * 𝓛 α ^ 4 * 𝓛 α ^ 4 / 2⁻¹ ^ 24 +
            2 ^ 203 * i * 𝓛 α ^ 8 := by have := hα₀.trans_le hαβ; gcongr
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
  obtain ⟨V, _, _, _, _, B, hV, hB, hαβ, hBV⟩ := ind ⌊𝓛 α / log (65 / 64)⌋₊
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
      _ = ⌊(log (65 / 64) + log α⁻¹) / log (65 / 64)⌋₊ := by
        rw [add_comm (log _), ← div_add_one aux.ne', Nat.floor_add_one, Nat.cast_succ]
        exact div_nonneg (log_nonneg $ one_le_inv (by positivity) (by simp [α])) aux.le
      _ ≤ ⌊𝓛 α / log (65 / 64)⌋₊ := by
        gcongr
        calc
          log (65 / 64) ≤ 65/64 - 1 := log_le_sub_one_of_pos $ by norm_num
          _ ≤ 1 := by norm_num
    all_goals positivity
  rw [hB.dL2Inner_mu_conv_mu_mu_two_smul_mu] at hBV
  suffices h : (q ^ (n - 2 ^ 210 * 𝓛 α ^ 9) : ℝ) ≤ q ^ (n / 2) by
    rwa [rpow_le_rpow_left_iff ‹_›, sub_le_comm, sub_half, div_le_iff₀' zero_lt_two, ← mul_assoc,
      ← pow_succ'] at h
  calc
    _ ≤ ↑q ^ (finrank (ZMod q) V : ℝ) := by
      gcongr
      · assumption
      rw [sub_le_comm]
      calc
        n - finrank (ZMod q) V ≤ 2 ^ 203 * ⌊𝓛 α / log (65 / 64)⌋₊ * 𝓛 α ^ 8 := by
          rwa [sub_le_iff_le_add']
        _ ≤ 2 ^ 203 * (𝓛 α / log (65 / 64)) * 𝓛 α ^ 8 := by
          gcongr; exact Nat.floor_le (by positivity)
        _ = 2 ^ 203 * (log (65 / 64)) ⁻¹ * 𝓛 α ^ 9 := by ring
        _ ≤ 2 ^ 203 * 2 ^ 7 * 𝓛 α ^ 9 := by
          gcongr
          rw [inv_le ‹_› (by positivity)]
          calc
            (2 ^ 7)⁻¹ ≤ 1 - (65 / 64)⁻¹ := by norm_num
            _ ≤ log (65 / 64) := one_sub_inv_le_log_of_pos (by positivity)
        _ = 2 ^ 210 * 𝓛 α ^ 9 := by ring
    _ = ↑(card V) := by simp [card_eq_pow_finrank (K := ZMod q) (V := V)]
    _ ≤ 2 * β⁻¹ ^ 2 := by
      rw [← natCast_card_mul_nnratCast_dens, mul_pow, mul_inv, ← mul_assoc,
        ← div_eq_mul_inv (card V : ℝ), ← zpow_one_sub_natCast₀ (by positivity)] at hBV
      have : 0 < (card V : ℝ) := by positivity
      simpa [le_inv_mul_iff₀, mul_inv_le_iff₀, this, zero_lt_two, mul_comm] using hBV
    _ ≤ 2 * α⁻¹ ^ 2 := by gcongr
    _ ≤ _ := hα
  simpa [card_eq_pow_finrank (K := ZMod q) (V := V), ZMod.card] using hq'.pow
