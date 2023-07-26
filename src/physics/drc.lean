import logic.lemmas
import mathlib.algebra.big_operators.ring
import mathlib.data.complex.exponential
import mathlib.data.finset.basic
import mathlib.data.fintype.lattice
import mathlib.data.real.sqrt
import prereqs.convolution.norm

/-!
# Dependent Random Choice
-/

open real finset
open_locale big_operators nnreal pointwise

variables {G : Type*} [decidable_eq G] [fintype G] [add_comm_group G] {p : ℕ} {B₁ B₂ A : finset G}
  {ε δ : ℝ}

/-- Auxiliary definition for the Dependent Random Choice step. We intersect `B₁` and `B₂` with
`C p A s` for some `s`. -/
private def C (p : ℕ) (A : finset G) (s : fin p → G) : finset G := univ.inf (λ i, s i +ᵥ A)

private lemma lemma_0 (p : ℕ) (B₁ B₂ A : finset G) (f : G → ℝ) :
  ∑ s, ⟪𝟭_[ℝ] (B₁ ∩ C p A s) ○ 𝟭 (B₂ ∩ C p A s), f⟫_[ℝ] =
    (B₁.card * B₂.card) • ∑ x, (μ_[ℝ] B₁ ○ μ B₂) x * (𝟭 A ○ 𝟭 A) x ^ p * f x :=
begin
  simp_rw mul_assoc,
  simp only [L2inner_eq_sum, is_R_or_C.conj_to_real, mul_sum, sum_mul,
    smul_sum, @sum_comm _ _ (fin p → G), sum_dconv_mul, dconv_apply_sub, fintype.sum_pow,
    map_indicate],
  congr' with b₁,
  congr' with b₂,
  refine fintype.sum_equiv (equiv.neg $ fin p → G) _ _ (λ s, _),
  rw [←smul_mul_assoc, ←smul_mul_smul, card_smul_mu_apply, card_smul_mu_apply,
    indicate_inter_apply, indicate_inter_apply, mul_mul_mul_comm, prod_mul_distrib],
  simp [C, indicate_inf_apply, ←translate_indicate, sub_eq_add_neg, mul_assoc],
end

private lemma sum_C (p : ℕ) (B A : finset G) : ∑ s, (B ∩ C p A s).card = A.card ^ p * B.card :=
begin
  simp only [card_eq_sum_indicate, indicate_inter_apply, C, indicate_inf_apply, mul_sum, sum_mul,
    sum_pow', @sum_comm _ G, fintype.pi_finset_univ, ←translate_indicate, translate_apply],
  congr' with x,
  exact fintype.sum_equiv (equiv.sub_left $ λ _, x) _ _ (λ s, mul_comm _ _),
end

private lemma sum_cast_C (p : ℕ) (B A : finset G) :
  ∑ s, ((B ∩ C p A s).card : ℝ) = A.card ^ p * B.card :=
by rw [←nat.cast_sum, sum_C]; norm_cast

/-- If `A` is nonempty, and `B₁` and `B₂` intersect, then the `μ B₁ ○ μ B₂`-weighted Lp norm of
`𝟭 A ○ 𝟭 A` is positive. -/
private lemma Lpnorm_conv_pos (hp : p ≠ 0) (hB : (B₁ ∩ B₂).nonempty) (hA : A.nonempty) :
  0 < ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ p :=
begin
  rw wLpnorm_pow_eq_sum,
  refine sum_pos' (λ x _, smul_nonneg zero_le' $ by positivity) ⟨0, mem_univ _,
    smul_pos _ $ pow_pos _ _⟩,
  { refine lt_of_le_of_ne' (dconv_nonneg mu_nonneg mu_nonneg _) _,
    rwa [←function.mem_support, support_dconv, support_mu, support_mu, ←coe_sub, mem_coe,
      zero_mem_sub_iff, not_disjoint_iff_nonempty_inter]; exact mu_nonneg },
  { rw [norm_pos_iff, ←function.mem_support, support_dconv, support_indicate],
    exact hA.to_set.zero_mem_sub,
    all_goals { positivity } },
  { positivity }
end

lemma drc (hp₂ : 2 ≤ p) (f : G → ℝ≥0) (hf : 0 < ∑ x, (μ_[ℝ] B₁ ○ μ B₂) x * (𝟭 A ○ 𝟭 A) x ^ p * f x)
  (hB : (B₁ ∩ B₂).nonempty) (hA : A.nonempty) :
  ∃ (A₁ ⊆ B₁) (A₂ ⊆ B₂), ⟪μ_[ℝ] A₁ ○ μ A₂, coe ∘ f⟫_[ℝ] * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ p ≤
    2 * ∑ x, (μ B₁ ○ μ B₂) x * (𝟭 A ○ 𝟭 A) x ^ p * f x ∧
    (4 : ℝ)⁻¹ * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) / A.card ^ (2 * p) ≤ A₁.card / B₁.card ∧
    (4 : ℝ)⁻¹ * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) / A.card ^ (2 * p) ≤ A₂.card / B₂.card :=
begin
  have := hA.card_pos,
  have := (hB.mono $ inter_subset_left _ _).card_pos,
  have := (hB.mono $ inter_subset_right _ _).card_pos,
  have hp₀ : p ≠ 0 := by positivity,
  have := Lpnorm_conv_pos hp₀ hB hA,
  set M : ℝ := 2⁻¹ * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ p * (sqrt B₁.card * sqrt B₂.card) /
    A.card ^ p with hM_def,
  have hM : 0 < M := by rw hM_def; positivity,
  set A₁ := λ s, B₁ ∩ C p A s,
  set A₂ := λ s, B₂ ∩ C p A s,
  set g : (fin p → G) → ℝ := λ s, (A₁ s).card * (A₂ s).card with hg_def,
  have hg : ∀ s, 0 ≤ g s := λ s, by rw hg_def; dsimp; positivity,
  have hgB : ∑ s, g s = B₁.card * B₂.card * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ p,
  { have hAdconv : 0 ≤ 𝟭_[ℝ] A ○ 𝟭 A := dconv_nonneg indicate_nonneg indicate_nonneg,
    simpa only [wLpnorm_pow_eq_sum hp₀, L2inner_eq_sum, sum_dconv, sum_indicate, pi.one_apply,
      is_R_or_C.inner_apply, is_R_or_C.conj_to_real, norm_of_nonneg (hAdconv _), mul_one,
      nsmul_eq_mul, nat.cast_mul, ←hg_def, nnreal.smul_def, nnreal.coe_dconv, nnreal.coe_comp_mu]
      using lemma_0 p B₁ B₂ A 1 },
  suffices : ∑ s, ⟪𝟭_[ℝ] (A₁ s) ○ 𝟭 (A₂ s), coe ∘ f⟫_[ℝ] * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ p <
    ∑ s, 𝟭 (univ.filter $ λ s, M ^ 2 ≤ g s) s * g s *
      (2 * ∑ x, (μ B₁ ○ μ B₂) x * (𝟭 A ○ 𝟭 A) x ^ p * f x),
  { obtain ⟨s, -, hs⟩ := exists_lt_of_sum_lt this,
    refine ⟨_, inter_subset_left _ (C p A s), _, inter_subset_left _ (C p A s), _⟩,
    simp only [indicate_apply, mem_filter, mem_univ, true_and, boole_mul] at hs,
    split_ifs at hs, swap,
    { simp only [zero_mul, L2inner_eq_sum, function.comp_app, is_R_or_C.inner_apply,
        is_R_or_C.conj_to_real] at hs,
      have : 0 ≤ 𝟭_[ℝ] (A₁ s) ○ 𝟭 (A₂ s) := by positivity,
      cases hs.not_le (mul_nonneg (sum_nonneg $ λ x _, mul_nonneg (this _) $ by positivity) $
        by positivity) },
    have : (4 : ℝ)⁻¹ * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) / A.card ^ (2 * p) ≤
      (A₁ s).card / B₁.card * ((A₂ s).card / B₂.card),
    { rw [div_mul_div_comm, le_div_iff],
      simpa [hg_def, hM_def, mul_pow, pow_mul', show (2 : ℝ) ^ 2 = 4, by norm_num,
        mul_div_right_comm] using h,
      positivity },
    refine ⟨(lt_of_mul_lt_mul_left (hs.trans_eq' _) $ hg s).le, this.trans $ mul_le_of_le_one_right
      _ $ div_le_one_of_le _ _, this.trans $ mul_le_of_le_one_left _ $ div_le_one_of_le _ _⟩,
    { simp_rw [←card_smul_mu, smul_dconv, dconv_smul, L2inner_smul_left, star_trivial, hg_def,
        nsmul_eq_mul, mul_assoc] },
    any_goals { positivity },
    all_goals { exact nat.cast_le.2 (card_mono $ inter_subset_left _ _) } },
  rw [←sum_mul, lemma_0, nsmul_eq_mul, nat.cast_mul, ←sum_mul, mul_right_comm, ←hgB, mul_left_comm,
    ←mul_assoc],
  simp only [indicate_apply, boole_mul, mem_filter, mem_univ, true_and, ←sum_filter,
    mul_lt_mul_right hf, function.comp_app],
  by_cases h : ∀ s, g s ≠ 0 → M ^ 2 ≤ g s,
  { rw [←@sum_filter_ne_zero _ _ (filter _ _), finset.filter_comm,
    filter_true_of_mem (λ s hs, h s (mem_filter.1 hs).2), ←sum_filter_ne_zero],
    refine lt_mul_of_one_lt_left (sum_pos (λ s hs, (h _ (mem_filter.1 hs).2).trans_lt' $
      by positivity) _) one_lt_two,
    rw ←sum_filter_ne_zero at hgB,
    exact nonempty_of_sum_ne_zero (hgB.trans_ne $ by positivity) },
  push_neg at h,
  obtain ⟨s, hs⟩ := h,
  suffices h : (2 : ℝ) * ∑ s with g s < M ^ 2, g s < ∑ s, g s,
  { refine (le_or_lt_of_add_le_add _).resolve_left h.not_le,
    simp_rw [←not_le, ←compl_filter, ←two_mul, ←mul_add, sum_compl_add_sum] },
  rw [←lt_div_iff' (zero_lt_two' ℝ), div_eq_inv_mul],
  calc
      ∑ s with g s < M ^ 2, g s
      = ∑ s with g s < M ^ 2 ∧ g s ≠ 0, sqrt (g s) * sqrt (g s)
      : by simp_rw [mul_self_sqrt (hg _), ←filter_filter, sum_filter_ne_zero]
  ... < ∑ s with g s < M ^ 2 ∧ g s ≠ 0, M * sqrt (g s)
      : sum_lt_sum_of_nonempty ⟨s, mem_filter.2 ⟨mem_univ _, hs.symm⟩⟩ _
  ... ≤ ∑ s, M * sqrt (g s) : sum_le_univ_sum_of_nonneg $ λ s, by positivity
  ... = M * ∑ s, sqrt (A₁ s).card * sqrt (A₂ s).card
      : by simp_rw [mul_sum, sqrt_mul (nat.cast_nonneg _)]
  ... ≤ M * (sqrt (∑ s, (A₁ s).card) * sqrt (∑ s, (A₂ s).card))
      : mul_le_mul_of_nonneg_left
          (sum_sqrt_mul_sqrt_le _ (λ i, by positivity) $ λ i, by positivity) hM.le
  ... = _ : _,
  { simp only [mem_filter, mem_univ, true_and, nat.cast_nonneg, and_imp],
    exact λ s hsM hs,
      mul_lt_mul_of_pos_right ((sqrt_lt' hM).2 hsM) (sqrt_pos.2 $ (hg _).lt_of_ne' hs) },
  rw [sum_cast_C, sum_cast_C, sqrt_mul', sqrt_mul', mul_mul_mul_comm (sqrt _), mul_self_sqrt,
    ←mul_assoc, hM_def, div_mul_cancel, ←sqrt_mul, mul_assoc, mul_self_sqrt, hgB,
    mul_right_comm, mul_assoc],
  all_goals { positivity },
end

noncomputable def S (p : ℝ≥0) (ε : ℝ) (B₁ B₂ A : finset G) : finset G :=
univ.filter $ λ x, (1 - ε) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] < (𝟭 A ○ 𝟭 A) x

@[simp] lemma mem_S {p : ℝ≥0} {ε : ℝ} {B₁ B₂ A : finset G} {x : G} :
  x ∈ S p ε B₁ B₂ A ↔ (1 - ε) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] < (𝟭 A ○ 𝟭 A) x :=
by simp [S]

--TODO: When `1 < ε`, the result is trivial since `S = univ`.
lemma sifting (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hp : even p) (hp₂ : 2 ≤ p)
  (hpε : ε⁻¹ * log (2 / δ) ≤ p) (hB : (B₁ ∩ B₂).nonempty) (hA : A.nonempty)
  (hf : 0 < ∑ x, (μ_[ℝ] B₁ ○ μ B₂) x * (𝟭 A ○ 𝟭 A) x ^ p * 𝟭_[ℝ≥0] (S p ε B₁ B₂ A)ᶜ x) :
  ∃ (A₁ ⊆ B₁) (A₂ ⊆ B₂), 1 - δ ≤ ∑ x in S p ε B₁ B₂ A, (μ A₁ ○ μ A₂) x ∧
    (4 : ℝ)⁻¹ * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) / A.card ^ (2 * p) ≤ A₁.card / B₁.card ∧
    (4 : ℝ)⁻¹ * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) / A.card ^ (2 * p) ≤ A₂.card / B₂.card :=
begin
  obtain ⟨A₁, hAB₁, A₂, hAB₂, h, hcard₁, hcard₂⟩ := drc hp₂ (𝟭 (S p ε B₁ B₂ A)ᶜ) hf hB hA,
  refine ⟨A₁, hAB₁, A₂, hAB₂, _, hcard₁, hcard₂⟩,
  have hp₀ : 0 < p := by positivity,
  have aux : ∀ (C : finset G) r,
    (4 : ℝ)⁻¹ * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) / A.card ^ (2 * p) ≤ C.card / r →
      C.nonempty,
  { simp_rw nonempty_iff_ne_empty,
    rintro C r h rfl,
    simp [pow_mul', (zero_lt_four' ℝ).not_le, inv_mul_le_iff (zero_lt_four' ℝ), mul_assoc,
      div_nonpos_iff, mul_nonpos_iff, (pow_pos (Lpnorm_conv_pos hp₀.ne' hB hA) 2).not_le] at h,
    norm_cast at h,
    simpa [hp₀, hA.ne_empty] using h },
  have hA₁ : A₁.nonempty := aux _ _ hcard₁,
  have hA₂ : A₂.nonempty := aux _ _ hcard₂,
  clear hcard₁ hcard₂ aux,
  rw [sub_le_comm],
  calc
      _ = ∑ x in (S p ε B₁ B₂ A)ᶜ, (μ A₁ ○ μ A₂) x : _
    ... = ⟪μ_[ℝ] A₁ ○ μ A₂, coe ∘ 𝟭_[ℝ≥0] (S ↑p ε B₁ B₂ A)ᶜ⟫_[ℝ]
        : by simp [L2inner_eq_sum, -mem_compl, -mem_S, apply_ite coe, indicate_apply]
    ... ≤ _ : (le_div_iff $ Lpnorm_conv_pos hp₀.ne' hB hA).2 h
    ... ≤ _ : _,
  { simp_rw [sub_eq_iff_eq_add', sum_add_sum_compl, sum_dconv, map_mu],
    rw [sum_mu _ hA₁, sum_mu _ hA₂, one_mul]; apply_instance },
  rw [div_le_iff (Lpnorm_conv_pos hp₀.ne' hB hA), ←le_div_iff' (zero_lt_two' ℝ)],
  simp only [apply_ite coe, indicate_apply, nonneg.coe_one, nonneg.coe_zero, mul_boole,
    sum_ite_mem, univ_inter, mul_div_right_comm],
  calc
      ∑ x in (S p ε B₁ B₂ A)ᶜ, (μ B₁ ○ μ B₂) x * (𝟭 A ○ 𝟭 A) x ^ p ≤ ∑ x in (S p ε B₁ B₂ A)ᶜ,
        (μ B₁ ○ μ B₂) x * ((1 - ε) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂]) ^ p
        : sum_le_sum $ λ x hx, mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left
          (dconv_nonneg indicate_nonneg indicate_nonneg _) (by simpa using hx) _)
          (dconv_nonneg mu_nonneg mu_nonneg _)
    ... ≤ ∑ x, (μ B₁ ○ μ B₂) x * ((1 - ε) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂]) ^ p
        : sum_le_univ_sum_of_nonneg $ λ x,
            mul_nonneg (dconv_nonneg mu_nonneg mu_nonneg _) $ hp.pow_nonneg _
    ... = ‖μ_[ℝ] B₁‖_[1] * ‖μ_[ℝ] B₂‖_[1] * ((1 - ε) ^ p * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ p) : _
    ... ≤ _ : mul_le_of_le_one_left (mul_nonneg (hp.pow_nonneg _) $ hp.pow_nonneg _) $
          mul_le_one L1norm_mu_le_one Lpnorm_nonneg L1norm_mu_le_one
    ... ≤ _ : mul_le_mul_of_nonneg_right _ $ hp.pow_nonneg _,
  { have : 0 ≤ μ_[ℝ] B₁ ○ μ B₂ := dconv_nonneg mu_nonneg mu_nonneg,
    simp_rw [←L1norm_dconv mu_nonneg mu_nonneg, L1norm_eq_sum, norm_of_nonneg (this _), sum_mul,
      mul_pow] },
  calc
    (1 - ε) ^ p ≤ exp (-ε) ^ p : pow_le_pow_of_le_left (sub_nonneg.2 hε₁) (one_sub_le_exp_neg _) _
    ... = exp (-(ε * p)) : by rw [←neg_mul, exp_mul, rpow_nat_cast]
    ... ≤ exp (-log (2 / δ)) : exp_monotone $ neg_le_neg $ (inv_mul_le_iff $ by positivity).1 hpε
    ... = δ / 2 : by rw [exp_neg, exp_log, inv_div]; positivity,
end
