import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Analysis.RCLike.Inner
import Mathlib.Data.Complex.ExponentialBounds
import LeanAPAP.Prereqs.Convolution.Discrete.Defs
import LeanAPAP.Prereqs.Function.Indicator.Complex
import LeanAPAP.Prereqs.LpNorm.Weighted

/-!
# Unbalancing
-/

open Finset hiding card
open Fintype (card)
open Function MeasureTheory RCLike Real
open scoped ComplexConjugate ComplexOrder NNReal ENNReal mu

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  {ν : G → ℝ≥0} {f : G → ℝ} {g h : G → ℂ} {ε : ℝ} {p : ℕ}

/-- Note that we do the physical proof in order to avoid the Fourier transform. -/
lemma pow_inner_nonneg' {f : G → ℂ} (hf : g ○ g = f) (hν : h ○ h = (↑) ∘ ν) (k : ℕ) :
    0 ≤ ⟪f ^ k, (↑) ∘ ν⟫_[ℂ] := by
  suffices
    ⟪f ^ k, (↑) ∘ ν⟫_[ℂ] = ∑ z : Fin k → G, (‖∑ x, (∏ i, conj (g (x + z i))) * h x‖ : ℂ) ^ 2 by
    rw [this]
    positivity
  rw [← hf, ← hν, wInner_one_eq_sum]
  simp only [WithLp.equiv_symm_pi_apply, Pi.pow_apply, RCLike.inner_apply, map_pow]
  simp_rw [dconv_apply h, mul_sum]
  --TODO: Please make `conv` work here :(
  have : ∀ x, ∀ yz ∈ ({yz : G × G | yz.1 - yz.2 = x} : Finset _),
    conj ((g ○ g) x) ^ k * (h yz.1 * conj (h yz.2)) =
      conj ((g ○ g) (yz.1 - yz.2)) ^ k * (h yz.1 * conj (h yz.2)) := by
    simp only [mem_filter, mem_univ, true_and]
    rintro _ _ rfl
    rfl
  refine (sum_congr rfl fun _ _ ↦ sum_congr rfl $ this _).trans ?_
  simp_rw [dconv_apply_sub, sum_fiberwise, ← univ_product_univ, sum_product]
  simp only [sum_pow', sum_mul_sum, map_mul, starRingEnd_self_apply, Fintype.piFinset_univ,
    ← Complex.conj_mul', sum_product, map_sum, map_prod,
    mul_mul_mul_comm (g _), ← prod_mul_distrib]
  simp only [sum_mul, @sum_comm _ _ (Fin k → G), mul_comm (conj _), prod_mul_distrib]
  rw [sum_comm]
  congr with x
  congr with y
  congr with z
  rw [mul_mul_mul_comm _ _ _ (h _), mul_comm (h _)]

/-- Note that we do the physical proof in order to avoid the Fourier transform. -/
lemma pow_inner_nonneg {f : G → ℝ} (hf : g ○ g = (↑) ∘ f) (hν : h ○ h = (↑) ∘ ν) (k : ℕ) :
    (0 : ℝ) ≤ ⟪(↑) ∘ ν, f ^ k⟫_[ℝ] := by
  simpa [← Complex.zero_le_real, wInner_one_eq_sum, mul_comm] using pow_inner_nonneg' hf hν k

private lemma log_ε_pos (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) : 0 < log (3 / ε) :=
  log_pos $ (one_lt_div hε₀).2 $ hε₁.trans_lt $ by norm_num

private lemma p'_pos (hp : 5 ≤ p) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) : 0 < 24 / ε * log (3 / ε) * p := by
  have := log_ε_pos hε₀ hε₁; positivity

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- Note that we do the physical proof in order to avoid the Fourier transform. -/
private lemma unbalancing'' (p : ℕ) (hp : 5 ≤ p) (hp₁ : Odd p) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (hf : g ○ g = (↑) ∘ f) (hν : h ○ h = (↑) ∘ ν) (hν₁ : ‖((↑) ∘ ν : G → ℝ)‖_[1] = 1)
    (hε : ε ≤ ‖f‖_[p, ν]) :
    1 + ε / 2 ≤ ‖f + 1‖_[.ofReal (24 / ε * log (3 / ε) * p), ν] := by
  simp only [dL1Norm_eq_sum_nnnorm, NNReal.nnnorm_eq, Function.comp_apply] at hν₁
  obtain hf₁ | hf₁ := le_total 2 ‖f + 1‖_[2 * p, ν]
  · calc
      1 + ε / 2 ≤ 1 + 1 / 2 := add_le_add_left (div_le_div_of_nonneg_right hε₁ zero_le_two) _
      _ ≤ 2 := by norm_num
      _ ≤ ‖f + 1‖_[2 * p, ν] := hf₁
      _ ≤ _ := wLpNorm_mono_right ?_ _ _
    norm_cast
    rw [ENNReal.natCast_le_ofReal (by positivity)]
    push_cast
    gcongr
    calc
      2 ≤ 24 / 1 * 0.6931471803 := by norm_num
      _ ≤ 24 / ε * log (3 / ε) :=
        mul_le_mul (div_le_div_of_nonneg_left (by norm_num) hε₀ hε₁)
          (log_two_gt_d9.le.trans
            (log_le_log zero_lt_two $
              (div_le_div_of_nonneg_left (by norm_num) hε₀ hε₁).trans' $ by norm_num))
          (by norm_num) ?_
    all_goals positivity
  have : ε ^ p ≤ 2 * ∑ i, ↑(ν i) * ((f ^ (p - 1)) i * f⁺ i) := by
    calc
      ε ^ p ≤ ‖f‖_[p, ν] ^ p := hp₁.strictMono_pow.monotone hε
      _ = ∑ i, ν i • ((f ^ (p - 1)) i * |f| i) := ?_
      _ ≤ ⟪((↑) ∘ ν : G → ℝ), f ^ p⟫_[ℝ] + ∑ i, ↑(ν i) * ((f ^ (p - 1)) i * |f| i) :=
        (le_add_of_nonneg_left $ pow_inner_nonneg hf hν _)
      _ = _ := ?_
    · norm_cast
      rw [wLpNorm_pow_eq_sum_nnnorm hp₁.pos.ne']
      push_cast
      dsimp
      refine sum_congr rfl fun i _ ↦ ?_
      rw [← abs_of_nonneg ((Nat.Odd.sub_odd hp₁ odd_one).pow_nonneg $ f _), abs_pow,
        pow_sub_one_mul hp₁.pos.ne', NNReal.smul_def, smul_eq_mul]
    · simp [wInner_one_eq_sum, ← sum_add_distrib, ← mul_add, ← pow_sub_one_mul hp₁.pos.ne' (f _),
        mul_sum, mul_left_comm (2 : ℝ), add_abs_eq_two_nsmul_posPart]
  set P : Finset _ := {i | 0 ≤ f i}
  set T : Finset _ := {i | 3 / 4 * ε ≤ f i}
  have hTP : T ⊆ P := monotone_filter_right _ fun i ↦ le_trans $ by positivity
  have : 2⁻¹ * ε ^ p ≤ ∑ i ∈ P, ↑(ν i) * (f ^ p) i := by
    rw [inv_mul_le_iff₀ (zero_lt_two' ℝ), sum_filter]
    convert this using 3
    rw [Pi.posPart_apply, posPart_eq_ite]
    split_ifs <;> simp [pow_sub_one_mul hp₁.pos.ne']
  have hp' : 1 ≤ (2 * p : ℝ≥0) := by
    norm_cast
    rw [Nat.succ_le_iff]
    positivity
  have : ∑ i ∈ P \ T, ↑(ν i) * (f ^ p) i ≤ 4⁻¹ * ε ^ p := by
    calc
      _ ≤ ∑ i ∈ P \ T, ↑(ν i) * (3 / 4 * ε) ^ p := sum_le_sum fun i hi ↦ ?_
      _ = (3 / 4) ^ p * ε ^ p * ∑ i ∈ P \ T, (ν i : ℝ) := by rw [← sum_mul, mul_comm, mul_pow]
      _ ≤ 4⁻¹ * ε ^ p * ∑ i, (ν i : ℝ) := ?_
      _ = 4⁻¹ * ε ^ p := by norm_cast; simp [hν₁]
    · simp only [mem_sdiff, mem_filter, mem_univ, true_and, not_le, P, T] at hi
      cases hi
      dsimp
      gcongr
    · refine mul_le_mul (mul_le_mul_of_nonneg_right (le_trans (pow_le_pow_of_le_one ?_ ?_ hp) ?_)
        ?_) (sum_le_univ_sum_of_nonneg fun i ↦ ?_) ?_ ?_ <;>
        first
        | positivity
        | norm_num
  replace hf₁ : ‖f‖_[2 * p, ν] ≤ 3 := by
    calc
      _ ≤ ‖f + 1‖_[2 * p, ν] + ‖(1 : G → ℝ)‖_[2 * p, ν] :=
        wLpNorm_le_add_wLpNorm_add (mod_cast hp') _ _ _
      _ ≤ 2 + 1 := by
        gcongr
        have : 2 * (p : ℝ≥0∞) ≠ 0 := mul_ne_zero two_ne_zero (by positivity)
        simp [wLpNorm_one, ENNReal.mul_ne_top, *]
      _ = 3 := by norm_num
  replace hp' := zero_lt_one.trans_le hp'
  have : 4⁻¹ * ε ^ p ≤ sqrt (∑ i ∈ T, ν i) * 3 ^ p := by
    calc
      4⁻¹ * ε ^ p = 2⁻¹ * ε ^ p - 4⁻¹ * ε ^ p := by rw [← sub_mul]; norm_num
      _ ≤ _ := (sub_le_sub ‹_› ‹_›)
      _ = ∑ i ∈ T, ν i * (f ^ p) i := by rw [sum_sdiff_eq_sub hTP, sub_sub_cancel]
      _ ≤ ∑ i ∈ T, ν i * |(f ^ p) i| :=
        (sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (le_abs_self _) ?_)
      _ = ∑ i ∈ T, sqrt (ν i) * sqrt (ν i * |(f ^ (2 * p)) i|) := by simp [← mul_assoc, pow_mul']
      _ ≤ sqrt (∑ i ∈ T, ν i) * sqrt (∑ i ∈ T, ν i * |(f ^ (2 * p)) i|) :=
        (sum_sqrt_mul_sqrt_le _ (fun i ↦ ?_) fun i ↦ ?_)
      _ ≤ sqrt (∑ i ∈ T, ν i) * sqrt (∑ i, ν i * |(f ^ (2 * p)) i|) := by
        gcongr; exact T.subset_univ
      _ = sqrt (∑ i ∈ T, ν i) * ‖f‖_[2 * ↑p, ν] ^ p := ?_
      _ ≤ _ := by gcongr; exact mod_cast hf₁
    any_goals positivity
    rw [wLpNorm_eq_sum_nnnorm (mod_cast hp'.ne') (by simp [ENNReal.mul_ne_top])]
    norm_cast
    rw [← NNReal.rpow_mul_natCast]
    have : (p : ℝ) ≠ 0 := by positivity
    simp [mul_comm, this, Real.sqrt_eq_rpow]
  set p' := 24 / ε * log (3 / ε) * p
  have hp' : 0 < p' := p'_pos hp hε₀ hε₁
  have : 1 - 8⁻¹ * ε ≤ (∑ i ∈ T, ↑(ν i)) ^ p'⁻¹ := by
    rw [← div_le_iff₀, mul_div_assoc, ← div_pow, le_sqrt, mul_pow, ← pow_mul'] at this
    calc
      _ ≤ exp (-(8⁻¹ * ε)) := one_sub_le_exp_neg _
      _ = ((ε / 3) ^ p * (ε / 3) ^ (2 * p)) ^ p'⁻¹ := ?_
      _ ≤ _ := rpow_le_rpow ?_ ((mul_le_mul_of_nonneg_right ?_ ?_).trans this) ?_
    · rw [← pow_add, ← one_add_mul _ p, ← rpow_natCast, Nat.cast_mul, ← rpow_mul, ← div_eq_mul_inv,
        mul_div_mul_right, ← exp_log (_ : 0 < ε / 3), ← exp_mul, ← inv_div, log_inv, neg_mul,
        mul_div_left_comm, div_mul_cancel_right₀ (log_ε_pos hε₀ hε₁).ne']
      field_simp
      ring
      all_goals positivity
    any_goals positivity
    calc
      _ ≤ (1 / 3 : ℝ) ^ p := by gcongr
      _ ≤ (1 / 3) ^ 5 := pow_le_pow_of_le_one ?_ ?_ hp
      _ ≤ _ := ?_
    any_goals positivity
    all_goals norm_num
  calc
    1 + ε / 2 = 1 + 2⁻¹ * ε := by rw [div_eq_inv_mul]
    _ ≤ 1 + 17 / 32 * ε := (add_le_add_left (mul_le_mul_of_nonneg_right (by norm_num) hε₀.le) _)
    _ = 1 + 5 / 8 * ε - 3 / 32 * ε * 1 := by ring
    _ ≤ 1 + 5 / 8 * ε - 3 / 32 * ε * ε := (sub_le_sub_left (mul_le_mul_of_nonneg_left hε₁ ?_) _)
    _ = (1 - 8⁻¹ * ε) * (1 + 3 / 4 * ε) := by ring
    _ ≤ (∑ i ∈ T, ↑(ν i)) ^ p'⁻¹ * (1 + 3 / 4 * ε) := (mul_le_mul_of_nonneg_right ‹_› ?_)
    _ = (∑ i ∈ T, ↑(ν i) * |3 / 4 * ε + 1| ^ p') ^ p'⁻¹ := by
      rw [← sum_mul, mul_rpow, rpow_rpow_inv, abs_of_nonneg, add_comm] <;> positivity
    _ ≤ (∑ i ∈ T, ↑(ν i) * |f i + 1| ^ p') ^ p'⁻¹ :=
        rpow_le_rpow ?_ (sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (rpow_le_rpow ?_
          (abs_le_abs_of_nonneg ?_ $ add_le_add_right (mem_filter.1 hi).2 _) ?_) ?_) ?_
    _ ≤ (∑ i, ↑(ν i) * |f i + 1| ^ p') ^ p'⁻¹ :=
        rpow_le_rpow ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ ↦ ?_) ?_
    _ = _ := by
        rw [wLpNorm_eq_sum_nnnorm]
        simp [NNReal.smul_def, hp'.ne', p', (p'_pos hp hε₀ hε₁).le]
        positivity
        simp
  all_goals positivity

/-- The unbalancing step. Note that we do the physical proof in order to avoid the Fourier
transform. -/
lemma unbalancing' (p : ℕ) (hp : p ≠ 0) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (ν : G → ℝ≥0)
    (f : G → ℝ) (g h : G → ℂ) (hf : g ○ g = (↑) ∘ f) (hν : h ○ h = (↑) ∘ ν)
    (hν₁ : ‖((↑) ∘ ν : G → ℝ)‖_[1] = 1) (hε : ε ≤ ‖f‖_[p, ν]) :
    ∃ p' : ℕ, p' ≤ 2 ^ 10 * ε⁻¹ ^ 2 * p ∧ 1 + ε / 2 ≤ ‖f + 1‖_[p', ν] := by
  have := log_ε_pos hε₀ hε₁
  have :=
    calc
      5 = 2 * 1 + 3 := by norm_num
      _ ≤ 2 * p + 3
        := add_le_add_right (mul_le_mul_left' (Nat.one_le_iff_ne_zero.2 hp) _) _
  rw [← Nat.one_le_iff_ne_zero] at hp
  refine ⟨⌈120 / ε * log (3 / ε) * p⌉₊, ?_, ?_⟩
  · calc
      (⌈120 / ε * log (3 / ε) * p⌉₊ : ℝ)
        = ⌈120 * ε⁻¹ * log (3 * ε⁻¹) * p⌉₊ := by simp [div_eq_mul_inv]
      _ ≤ 2 * (120 * ε⁻¹ * log (3 * ε⁻¹) * p) := Nat.ceil_le_two_mul <|
        calc
          (2⁻¹ : ℝ) ≤ 120 * 1 * 1 * 1 := by norm_num
          _ ≤ 120 * ε⁻¹ * log (3 * ε⁻¹) * p := by
            gcongr
            · exact (one_le_inv₀ hε₀).2 hε₁
            · rw [← log_exp 1]
              gcongr
              calc
                exp 1 ≤ 2.7182818286 := exp_one_lt_d9.le
                _ ≤ 3 * 1 := by norm_num
                _ ≤ 3 * ε⁻¹ := by gcongr; exact (one_le_inv₀ hε₀).2 hε₁
            · exact mod_cast hp
      _ ≤ 2 * (120 * ε⁻¹ * (3 * ε⁻¹) * p) := by gcongr; exact Real.log_le_self (by positivity)
      _ ≤ 2 * (2 ^ 7 * ε⁻¹ * (2 ^ 2 * ε⁻¹) * p) := by gcongr <;> norm_num
      _ = 2 ^ 10 * ε⁻¹ ^ 2 * p := by ring
  calc
    1 + ε / 2 ≤ ↑‖f + 1‖_[.ofReal (24 / ε * log (3 / ε) * ↑(2 * p + 3)), ν] :=
      unbalancing'' (2 * p + 3) this ((even_two_mul _).add_odd $ by decide) hε₀ hε₁ hf hν hν₁ $
        hε.trans $ wLpNorm_mono_right
          (Nat.cast_le.2 $ le_add_of_le_left $ le_mul_of_one_le_left' one_le_two) _ _
    _ ≤ _ := wLpNorm_mono_right ?_ _ _
  norm_cast
  calc
    _ = 24 / ε * log (3 / ε) * ↑(2 * p + 3 * 1) := by simp
    _ ≤ 24 / ε * log (3 / ε) * ↑(2 * p + 3 * p) := by gcongr
    _ = 120 / ε * log (3 / ε) * p := by push_cast; ring
    _ ≤ ⌈120 / ε * log (3 / ε) * p⌉₊ := Nat.le_ceil _

/-- The unbalancing step. Note that we do the physical proof in order to avoid the Fourier
transform. -/
lemma unbalancing (p : ℕ) (hp : p ≠ 0) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (f : G → ℝ) (g h : G → ℂ)
    (hf : g ○ g = (↑) ∘ f) (hh : h ○ h = μ univ)
    (hε : ε ≤ ‖f‖_[p, μ univ]) :
    ∃ p' : ℕ, p' ≤ 2 ^ 10 * ε⁻¹ ^ 2 * p ∧ 1 + ε / 2 ≤ ‖f + 1‖_[p', μ univ] :=
  unbalancing' p hp ε hε₀ hε₁ _ _ g h hf
    (show _ = Complex.ofReal ∘ NNReal.toReal ∘ μ univ by simpa using hh)
    (by simp; simp [mu_univ_eq_const, ← const_def]) (by simpa [rpow_neg, inv_rpow] using hε)
