import logic.lemmas
import mathlib.algebra.big_operators.ring
import mathlib.data.complex.exponential
import mathlib.data.finset.basic
import mathlib.data.fintype.lattice
import mathlib.data.real.sqrt
import prereqs.convolution

/-!
# Dependent Random Choice
-/

open real
open_locale big_operators nnreal pointwise

open finset

variables {G : Type*} [decidable_eq G] [fintype G] [add_comm_group G] {p : ℕ} {B₁ B₂ A : finset G}
  {ε δ : ℝ}

def C (p : ℕ) (A : finset G) (s : fin p → G) : finset G := univ.inf (λ i, s i +ᵥ A)

private lemma lemma_0 (p : ℕ) (B₁ B₂ A : finset G) (f : G → ℝ) :
  ∑ s, ⟪𝟭_[ℝ] (B₁ ∩ C p A s) ○ 𝟭 (B₂ ∩ C p A s), f⟫_[ℝ] =
    (B₁.card * B₂.card) • ∑ x, (μ_[ℝ] B₁ ○ μ B₂) x * ((𝟭 A ○ 𝟭 A) x ^ p * f x) :=
begin
  simp only [L2inner_eq_sum, is_R_or_C.inner_apply, is_R_or_C.conj_to_real, mul_sum, sum_mul,
    smul_sum, @sum_comm _ _ (fin p → G), sum_dconv_mul, dconv_apply_sub, fintype.sum_pow,
    map_indicator],
  congr' with b₁,
  congr' with b₂,
  refine fintype.sum_equiv (equiv.neg $ fin p → G) _ _ (λ s, _),
  rw [←smul_mul_assoc, ←smul_mul_smul, card_smul_mu_apply, card_smul_mu_apply,
    indicator_inter_apply, indicator_inter_apply, mul_mul_mul_comm, prod_mul_distrib],
  simp [C, indicator_inf_apply, ←translate_indicator, sub_eq_add_neg, mul_assoc],
end

private lemma sum_C (p : ℕ) (B A : finset G) : ∑ s, (B ∩ C p A s).card = A.card ^ p * B.card :=
begin
  -- conv_lhs { simp only [card_eq_sum_indicator, indicator_inter, sum_comm, ←mul_sum] },
  sorry
end

private lemma sum_cast_C (p : ℕ) (B A : finset G) :
  ∑ s, ((B ∩ C p A s).card : ℝ) = A.card ^ p * B.card :=
by rw [←nat.cast_sum, sum_C]; norm_cast

/-- If `A` is nonempty, and `B₁` and `B₂` intersect, then the `μ B₁ ○ μ B₂`-weighted Lp norm of
`𝟭 A ○ 𝟭 A` is positive. -/
private lemma aux (hp : p ≠ 0) (hB : (B₁ ∩ B₂).nonempty) (hA : A.nonempty) :
  0 < ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ p :=
begin
  rw wLpnorm_pow_eq_sum,
  refine sum_pos' (λ x _, smul_nonneg zero_le' $ by positivity) ⟨0, mem_univ _,
    smul_pos _ $ pow_pos _ _⟩,
  { refine lt_of_le_of_ne' (dconv_nonneg mu_nonneg mu_nonneg _) _,
    rwa [←function.mem_support, support_dconv, support_mu, support_mu, ←coe_sub, mem_coe,
      zero_mem_sub_iff, not_disjoint_iff_nonempty_inter]; exact mu_nonneg },
  { rw [norm_pos_iff, ←function.mem_support, support_dconv, support_indicator],
    exact hA.to_set.zero_mem_sub,
    all_goals { positivity } },
  { positivity }
end

lemma drc (hp : even p) (hp₂ : 2 ≤ p) (f : G → ℝ≥0) (hB : (B₁ ∩ B₂).nonempty) (hA : A.nonempty) :
  ∃ (A₁ ⊆ B₁) (A₂ ⊆ B₂), ⟪μ_[ℝ] A₁ ○ μ A₂, coe ∘ f⟫_[ℝ] ≤
    2 * (∑ x, (μ B₁ ○ μ B₂) x * (𝟭 A ○ 𝟭 A) x ^ p * f x) / ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ p
    ∧ (4 : ℝ)⁻¹ * A.card ^ (-2 * p : ℤ) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p)
      ≤ A₁.card / B₁.card
    ∧ (4 : ℝ)⁻¹ * A.card ^ (-2 * p : ℤ) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p)
      ≤ A₂.card / B₂.card :=
begin
  have := hA.card_pos,
  have := (hB.mono $ inter_subset_left _ _).card_pos,
  have := (hB.mono $ inter_subset_right _ _).card_pos,
  have hp₀ : p ≠ 0 := by positivity,
  have := aux hp₀ hB hA,
  set M : ℝ := 2⁻¹ * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ p /
    (A.card ^ p * (sqrt B₁.card * sqrt B₂.card)) with hM_def,
  have hp₀ : p ≠ 0 := by positivity,
  have hM : 0 < M := by rw hM_def; positivity,
  set g : (fin p → G) → ℝ := λ s, (B₁ ∩ C p A s).card * (B₂ ∩ C p A s).card with hg_def,
  have hg : ∀ s, 0 ≤ g s := λ s, by rw hg_def; dsimp; positivity,
  have hgB := lemma_0 p B₁ B₂ A 1,
  simp only [L2inner_eq_sum, sum_dconv, sum_indicator, pi.one_apply, is_R_or_C.inner_apply,
    is_R_or_C.conj_to_real, mul_one, nsmul_eq_mul, nat.cast_mul, ←hg_def] at hgB,
  change ∑ s, g s = _ at hgB,
  have : (2 : ℝ)⁻¹ * ∑ s, g s < ∑ s in univ.filter (λ s, M ^ 2 ≤ g s), g s,
  { by_cases h : ∀ s, g s ≠ 0 → M ^ 2 ≤ g s,
    { rw [←@sum_filter_ne_zero _ _ (filter _ _), finset.filter_comm,
      filter_true_of_mem (λ s hs, h s (mem_filter.1 hs).2), ←sum_filter_ne_zero],
      refine mul_lt_of_lt_one_left (sum_pos (λ s hs, (h _ (mem_filter.1 hs).2).trans_lt' $
        by positivity) _) two_inv_lt_one,
      rw ←sum_filter_ne_zero at hgB,
      refine nonempty_of_sum_ne_zero (hgB.trans_ne _),
      sorry },
    push_neg at h,
    obtain ⟨s, hs⟩ := h,
    suffices h : ∑ s in univ.filter (λ s, g s < M ^ 2), g s < 2⁻¹ * ∑ s, g s,
    { refine (le_or_lt_of_add_le_add _).resolve_left h.not_le,
      simp_rw [←not_le, ←compl_filter, ←two_mul, mul_inv_cancel_left₀ (two_ne_zero' ℝ),
        sum_compl_add_sum] },
    calc
       ∑ s in univ.filter (λ s, g s < M ^ 2), g s
        = ∑ s in univ.filter (λ s, g s < M ^ 2 ∧ g s ≠ 0), sqrt (g s) * sqrt (g s)
        : by simp_rw [mul_self_sqrt (hg _), ←filter_filter, sum_filter_ne_zero]
    ... < ∑ s in univ.filter (λ s, g s < M ^ 2 ∧ g s ≠ 0), M * sqrt (g s)
        : sum_lt_sum_of_nonempty ⟨s, mem_filter.2 ⟨mem_univ _, hs.symm⟩⟩ _
    ... ≤ ∑ s, M * sqrt (g s) : sum_le_univ_sum_of_nonneg $ λ s, by positivity
    ... = M * ∑ s, sqrt (B₁ ∩ C p A s).card * sqrt (B₂ ∩ C p A s).card
        : by simp_rw [mul_sum, sqrt_mul (nat.cast_nonneg _)]
    ... ≤ M * (sqrt (∑ s, (B₁ ∩ C p A s).card) * sqrt (∑ s, (B₂ ∩ C p A s).card))
        : mul_le_mul_of_nonneg_left _ hM.le
    ... = _ : _,
    { simp only [mem_filter, mem_univ, true_and, nat.cast_nonneg, and_imp],
      exact λ s hsM hs,
        mul_lt_mul_of_pos_right ((sqrt_lt' hM).2 hsM) (sqrt_pos.2 $ (hg _).lt_of_ne' hs) },
    sorry,
    rw [sum_cast_C, sum_cast_C, sqrt_mul', sqrt_mul', mul_mul_mul_comm (sqrt _), mul_self_sqrt,
      hM_def, div_mul_cancel, wLpnorm_pow_eq_sum hp₀],
    simp only [L2inner_eq_sum, sum_dconv, sum_indicator, pi.one_apply, is_R_or_C.inner_apply,
      is_R_or_C.conj_to_real, mul_one, nsmul_eq_mul, nat.cast_mul, ←hg_def],
    rw [hgB, @mul_sum _ _ _ (_ * _)],
    congr' with x,
    have : 0 ≤ 𝟭_[ℝ] A ○ 𝟭 A := dconv_nonneg indicator_nonneg indicator_nonneg,
    rw norm_of_nonneg (this _),
    sorry,
    all_goals { positivity } },
  sorry
end

noncomputable def S (p : ℝ≥0) (ε : ℝ) (B₁ B₂ A : finset G) : finset G :=
univ.filter $ λ x, (1 - ε) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] < (𝟭 A ○ 𝟭 A) x

@[simp] lemma mem_S {p : ℝ≥0} {ε : ℝ} {B₁ B₂ A : finset G} {x : G} :
  x ∈ S p ε B₁ B₂ A ↔ (1 - ε) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] < (𝟭 A ○ 𝟭 A) x :=
by simp [S]

--TODO: When `1 < ε`, the result is trivial since `S = univ`.
lemma sifting (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hp : even p) (hp₂ : 2 ≤ p)
  (hpε : ε⁻¹ * log (2 / δ) ≤ p) (hB : (B₁ ∩ B₂).nonempty) (hA : A.nonempty) :
  ∃ (A₁ ⊆ B₁) (A₂ ⊆ B₂), 1 - δ ≤ ∑ x in S p ε B₁ B₂ A, (μ A₁ ○ μ A₂) x ∧
    (4 : ℝ)⁻¹ * A.card ^ (-2 * p : ℤ) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) ≤
      A₁.card / B₁.card ∧
    (4 : ℝ)⁻¹ * A.card ^ (-2 * p : ℤ) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) ≤
      A₂.card / B₂.card :=
begin
  obtain ⟨A₁, hAB₁, A₂, hAB₂, h, hcard₁, hcard₂⟩ := drc hp hp₂ (𝟭 (S p ε B₁ B₂ A)ᶜ) hB hA,
  refine ⟨A₁, hAB₁, A₂, hAB₂, _, hcard₁, hcard₂⟩,
  have hp₀ : p ≠ 0 := by positivity,
  have aux : ∀ (C : finset G) r,
    (4 : ℝ)⁻¹ * A.card ^ (-2 * p : ℤ) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) ≤
      C.card / r → C.nonempty,
  { simp_rw nonempty_iff_ne_empty,
    rintro C r h rfl,
    simp [pow_mul', (zero_lt_four' ℝ).not_le, inv_mul_le_iff (zero_lt_four' ℝ), mul_assoc,
      mul_nonpos_iff, (pow_pos (aux hp₀ hB hA) 2).not_le] at h,
    have : 0 < 2 * p := by positivity,
    norm_cast at h,
    simpa [this, hA.ne_empty] using h },
  have hA₁ : A₁.nonempty := aux _ _ hcard₁,
  have hA₂ : A₂.nonempty := aux _ _ hcard₂,
  clear hcard₁ hcard₂ aux,
  rw sub_le_comm,
  calc
      _ = ∑ x in (S p ε B₁ B₂ A)ᶜ, (μ A₁ ○ μ A₂) x : _
    ... = ⟪μ_[ℝ] A₁ ○ μ A₂, coe ∘ 𝟭_[ℝ≥0] (S ↑p ε B₁ B₂ A)ᶜ⟫_[ℝ]
        : by simp [L2inner_eq_sum, -mem_compl, -mem_S, apply_ite coe, indicator_apply]
    ... ≤ _ : h
    ... ≤ _ : _,
  { simp_rw [sub_eq_iff_eq_add', sum_add_sum_compl, sum_dconv, map_mu],
    rw [sum_mu _ hA₁, sum_mu _ hA₂, one_mul]; apply_instance },
  rw [div_le_iff (aux hp₀ hB hA), ←le_div_iff' (zero_lt_two' ℝ), mul_div_right_comm],
  simp only [apply_ite coe, indicator_apply, nonneg.coe_one, nonneg.coe_zero, mul_boole,
    sum_ite_mem, univ_inter],
  calc
      ∑ x in (S p ε B₁ B₂ A)ᶜ, (μ B₁ ○ μ B₂) x * (𝟭 A ○ 𝟭 A) x ^ p ≤ ∑ x in (S p ε B₁ B₂ A)ᶜ,
        (μ B₁ ○ μ B₂) x * ((1 - ε) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂]) ^ p
        : sum_le_sum $ λ x hx, mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left
          (dconv_nonneg indicator_nonneg indicator_nonneg _) (by simpa using hx) _)
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
