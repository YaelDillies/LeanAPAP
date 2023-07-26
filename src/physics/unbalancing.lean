import analysis.inner_product_space.pi_L2
import data.complex.exponential_bounds
import mathlib.algebra.big_operators.ring
import mathlib.algebra.order.lattice_group
import mathlib.analysis.special_functions.log.basic
import mathlib.data.complex.exponential
import mathlib.data.nat.order.basic
import prereqs.convolution

/-!
# Unbalancing
-/

open finset real
open_locale big_operators complex_conjugate complex_order nnreal

variables {G : Type*} [fintype G] [decidable_eq G] [add_comm_group G] {ν : G → ℝ≥0} {f : G → ℝ}
  {g h : G → ℂ} {p : ℝ≥0} {ε : ℝ}

/-- Note that we do the physical proof in order to avoid the Fourier transform. -/
lemma pow_inner_nonneg' {f : G → ℂ} (hf : f = g ○ g) (hν : coe ∘ ν = h ○ h) (k : ℕ) :
  (0 : ℂ) ≤ ⟪f ^ k, coe ∘ ν⟫_[ℂ] :=
begin
  suffices : ⟪f ^ k, coe ∘ ν⟫_[ℂ] = ∑ z : fin k → G, ‖∑ x, (∏ i, conj (g (x + z i))) * h x‖ ^ 2,
  { rw this,
    exact sum_nonneg (λ z _, by simp) },
  rw [hf, hν, L2inner_eq_sum],
  simp only [pi_Lp.equiv_symm_apply, pi.pow_apply, is_R_or_C.inner_apply, map_pow],
  simp_rw [dconv_apply h, mul_sum],
  --TODO: Please make `conv` work here :(
  have : ∀ x, ∀ yz ∈ univ.filter (λ yz : G × G, yz.1 - yz.2 = x),
    conj ((g ○ g) x) ^ k * (h yz.1 * conj (h yz.2)) =
      conj ((g ○ g) (yz.1 - yz.2)) ^ k * (h yz.1 * conj (h yz.2)),
  { simp only [mem_filter, mem_univ, true_and],
    rintro _ _ rfl,
    refl },
  simp_rw [sum_congr rfl (this _), dconv_apply_sub, sum_fiberwise, ←univ_product_univ, sum_product],
  simp only [sum_pow', sum_mul_sum, map_mul, star_ring_end_self_apply, fintype.pi_finset_univ,
    ←inner_self_eq_norm_sq_to_K, sum_product, is_R_or_C.inner_apply, map_sum, map_prod,
     mul_mul_mul_comm, ←prod_mul_distrib],
  simp only [sum_mul, @sum_comm _ _ (fin k → G), mul_comm (conj _)],
  exact sum_comm,
end

/-- Note that we do the physical proof in order to avoid the Fourier transform. -/
lemma pow_inner_nonneg {f : G → ℝ} (hf : coe ∘ f = g ○ g) (hν : coe ∘ ν = h ○ h) (k : ℕ) :
  (0 : ℝ) ≤ ⟪coe ∘ ν, f ^ k⟫_[ℝ] :=
by simpa [←complex.zero_le_real, L2inner_eq_sum, mul_comm] using pow_inner_nonneg' hf hν k

/-- Note that we do the physical proof in order to avoid the Fourier transform. -/
lemma unbalancing' (p : ℕ) (hp : 5 ≤ p) (hp₁ : odd p) (hν₁ : ‖(coe ∘ ν : G → ℝ)‖_[1] = 1)
  (hν : coe ∘ ν = h ○ h) (hf : coe ∘ f = g ○ g) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hε : ε ≤ ‖f‖_[p, ν]) :
  ∃ p' : ℕ, ↑p' ≤ 16 / ε * log (12 / ε) * p ∧ 1 + ε/2 ≤ ‖f + 1‖_[p', ν] :=
begin
  simp only [L1norm_eq_sum, nnreal.norm_eq] at hν₁,
  obtain hf₁ | hf₁ := le_total 2 (‖f + 1‖_[2 * p, ν]),
  { refine ⟨2 * p, _⟩,
    simp_rw [nat.cast_mul, nat.cast_two],
    refine ⟨mul_le_mul_of_nonneg_right _ $ by positivity, _⟩,
    { calc
          2 ≤ 16 / 1 * (6931471803 / 10000000000) : by norm_num
        ... ≤ 16 / ε * log (12 / ε) : mul_le_mul (div_le_div_of_le_left (by norm_num) hε₀ hε₁)
              (log_two_gt_d9.le.trans (log_le_log_of_le zero_lt_two $ (div_le_div_of_le_left
              (by norm_num) hε₀ hε₁).trans' $ by norm_num)) (by norm_num) (by positivity) },
    { calc
          (_ : ℝ) ≤ 1 + 1 / 2 : add_le_add_left (div_le_div_of_le zero_le_two hε₁) _
        ... ≤ 2 : by norm_num
        ... ≤ _ : hf₁ } },
  have : ε ^ p ≤ 2 * ∑ i, ↑(ν i) * ((f ^ (p - 1)) i * f⁺ i),
  { calc
      ε ^ p ≤ ‖f‖_[p, ν] ^ p : hp₁.strict_mono_pow.monotone hε
      ... = ∑ i, ν i • ((f ^ (p - 1)) i * |f| i) : _
      ... ≤ ⟪(coe ∘ ν : G → ℝ), f ^ p⟫_[ℝ] + ∑ i, ↑(ν i) * ((f ^ (p - 1)) i * |f| i)
          : le_add_of_nonneg_left $ pow_inner_nonneg hf hν _
      ... = _ : _,
    rw wLpnorm_pow_eq_sum hp₁.pos.ne',
    dsimp,
    refine sum_congr rfl (λ i _, _),
    rw [←abs_of_nonneg ((nat.odd.sub_odd hp₁ odd_one).pow_nonneg $ f _), abs_pow,
      pow_sub_one_mul hp₁.pos.ne'],
    simp [L2inner_eq_sum, ←sum_add_distrib, ←mul_add, ←pow_sub_one_mul hp₁.pos.ne' (f _), mul_sum,
      mul_left_comm (2 : ℝ), add_abs_eq_two_nsmul_pos_part] },
  set P := univ.filter (λ i, 0 ≤ f i) with hP,
  set T := univ.filter (λ i, 3/4 * ε ≤ f i) with hT,
  have hTP : T ⊆ P := monotone_filter_right _  (λ i, le_trans $ by positivity),
  have : 2⁻¹ * ε ^ p ≤ ∑ i in P,↑(ν i) * (f ^ p) i,
  { rw [inv_mul_le_iff (zero_lt_two' ℝ), sum_filter],
    convert this,
    ext i,
    rw [pi.pos_part_apply, pos_part_eq_ite],
    split_ifs; simp [pow_sub_one_mul hp₁.pos.ne'] },
  have hp' : 1 ≤ (2 * p : ℝ≥0),
  { norm_cast,
    rw nat.succ_le_iff,
    positivity },
  have : ∑ i in P \ T, ↑(ν i) * (f ^ p) i ≤ 4⁻¹ * ε ^ p,
  { calc
        _ ≤ ∑ i in P \ T, ↑(ν i) * (3/4 * ε) ^ p : sum_le_sum $ λ i hi, _
      ... = (3/4) ^ p * ε ^ p * ∑ i in P \ T, ν i : by rw [←sum_mul, mul_comm, mul_pow]
      ... ≤ 4⁻¹ * ε ^ p * ∑ i, ν i : _
      ... = 4⁻¹ * ε ^ p : by rw [hν₁, mul_one],
    { simp only [mem_sdiff, mem_filter, mem_univ, true_and, not_le] at hi,
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left hi.1 hi.2.le _) (by positivity) },
    { refine mul_le_mul (mul_le_mul_of_nonneg_right (le_trans (pow_le_pow_of_le_one _ _ hp) _) $ _)
        (sum_le_univ_sum_of_nonneg $ λ i, _) (sum_nonneg $ λ i _, _) _; positivity <|> norm_num } },
  replace hf₁ : ‖f‖_[2 * p, ν] ≤ 3,
  { calc
        _ ≤ ‖f + 1‖_[2 * p, ν] + ‖(1 : G → ℝ)‖_[2 * p, ν] : wLpnorm_le_add_wLpnorm_add hp' _ _ _
      ... ≤ (2 + 1 : ℝ) : add_le_add hf₁ (by rw [wLpnorm_one, hν₁, one_rpow]; positivity)
      ... = 3 : by norm_num },
  replace hp' := zero_lt_one.trans_le hp',
  have : 4⁻¹ * ε ^ p ≤ (∑ i, ν i) ^ (2⁻¹ : ℝ) * 3 ^ p,
  { calc
        4⁻¹ * ε ^ p = 2⁻¹ * ε ^ p - 4⁻¹ * ε ^ p : by rw ←sub_mul; norm_num
      ... ≤ _ : sub_le_sub ‹_› ‹_›
      ... = ∑ i in T, ν i * (f ^ p) i : by rw [sum_sdiff_eq_sub hTP, sub_sub_cancel]
      ... ≤ ∑ i in T, ν i * |(f ^ p) i|
          : sum_le_sum $ λ i _, mul_le_mul_of_nonneg_left (le_abs_self _) $ by positivity
      ... ≤ ∑ i, ν i * |(f ^ p) i| : sum_le_univ_sum_of_nonneg $ λ i, by positivity
      ... = ⟪λ i, ((ν i).sqrt : ℝ), λ i, (ν i).sqrt * |(f ^ p) i|⟫_[ℝ]
          : by simp [L2inner_eq_sum, ←mul_assoc]
      ... ≤ ‖λ i, ((ν i).sqrt : ℝ)‖_[2] * ‖λ i, ↑(ν i).sqrt * |(f ^ p) i|‖_[2]
          : L2inner_le_L2norm_mul_L2norm _ _
      ... = (∑ i, ν i) ^ (2⁻¹ : ℝ) * ‖f‖_[2 * ↑p, ν] ^ p : _
      ... ≤ _ : mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left wLpnorm_nonneg hf₁ _) $
              rpow_nonneg $ sum_nonneg $ λ i _, nnreal.coe_nonneg _,
    rw [wLpnorm_eq_sum hp'.ne', ←ennreal.coe_one, ←ennreal.coe_bit0],
    simp only [Lpnorm_eq_sum two_ne_zero, coe_sqrt, nnreal.zero_le_coe, nnreal.coe_bit0,
      nonneg.coe_one, rpow_two, pow_bit0_abs, sq_sqrt, abs_nonneg, nnreal.smul_def,
      mul_comm (2 : ℝ), rpow_mul, pi.pow_apply, abs_pow, norm_eq_abs, mul_pow, nonneg.coe_mul,
      nnreal.coe_nat_cast, rpow_nat_cast, algebra.id.smul_eq_mul, mul_inv_rev],
    rwa [rpow_mul, rpow_nat_inv_pow_nat],
    { exact rpow_nonneg (sum_nonneg $ λ i _, by positivity) },
    { positivity },
    { exact sum_nonneg (λ i _, by positivity) } },
  set p' : ℕ := sorry,
  have hp' : 0 < p' := sorry,
  refine ⟨p', _, _⟩,
  sorry,
  have : 1 - 8⁻¹ * ε ≤ (∑ i in T, ↑(ν i)) ^ (p'⁻¹ : ℝ),
  { calc
        _ ≤ exp (-(8⁻¹ * ε)) : one_sub_le_exp_neg _
      ... ≤ (ε / 10) ^ (2 * p / p' : ℝ) : _
      ... ≤ _ : _,
      sorry,
      sorry },
  calc
      1 + ε / 2 = 1 + 2⁻¹ * ε : by rw div_eq_inv_mul
    ... ≤ 1 + 17/32 * ε
        : add_le_add_left (mul_le_mul_of_nonneg_right (by norm_num) hε₀.le) _
    ... = 1 + 5/8 * ε - 3/32 * ε * 1 : by ring
    ... ≤ 1 + 5/8 * ε - 3/32 * ε * ε
        : sub_le_sub_left (mul_le_mul_of_nonneg_left hε₁ $ by positivity) _
    ... = (1 - 8⁻¹ * ε) * (1 + 3/4 * ε) : by ring
    ... ≤ (∑ i in T, ↑(ν i)) ^ (p'⁻¹ : ℝ) * (1 + 3/4 * ε)
        : mul_le_mul_of_nonneg_right ‹_› $ by positivity
    ... = (∑ i in T, ↑(ν i) * |3/4 * ε + 1| ^ p') ^ (p'⁻¹ : ℝ)
        : by rw [←sum_mul, mul_rpow (sum_nonneg $ λ i _, _), pow_nat_rpow_nat_inv, abs_of_nonneg,
            add_comm]; positivity
    ... ≤ (∑ i in T, ↑(ν i) * |f i + 1| ^ p') ^ (p'⁻¹ : ℝ)
        : rpow_le_rpow (sum_nonneg $ λ i _, by positivity) (sum_le_sum $ λ i hi,
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (by positivity) (abs_le_abs_of_nonneg
              (by positivity) $ add_le_add_right (mem_filter.1 hi).2 _) _) $ by positivity) $
                by positivity
    ... ≤ (∑ i, ↑(ν i) * |f i + 1| ^ p') ^ (p'⁻¹ : ℝ)
        : rpow_le_rpow (sum_nonneg $ λ i _, by positivity)
          (sum_le_sum_of_subset_of_nonneg (subset_univ _) $ λ i _ _, by positivity) (by positivity)
    ... = _ : by simp [wLpnorm_eq_sum, nnreal.smul_def, hp'.ne'],
end

/-- The unbalancing step. Note that we do the physical proof in order to avoid the Fourier
transform. -/
lemma unbalancing (hp : 1 ≤ p) (hν₁ : ‖(coe ∘ ν : G → ℝ)‖_[1] = 1) (hν : coe ∘ ν = h ○ h)
  (hf : coe ∘ f = g ○ g) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hε : ε ≤ ‖f‖_[p, ν]) :
  ∃ p' : ℝ≥0, ↑p' ≤ 16 / ε * log (48 / ε) * p ∧ 1 + ε/2 ≤ ‖f + 1‖_[p', ν] :=
sorry --TODO: Bhavik
