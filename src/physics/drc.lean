import mathlib.data.complex.exponential
import mathlib.data.real.sqrt
import prereqs.convolution

/-!
# Dependent Random Choice
-/

open real
open_locale big_operators nnreal

open finset

variables {G : Type*} [decidable_eq G] [fintype G] [add_comm_group G] {B₁ B₂ A : finset G} {ε δ : ℝ}
  {p : ℕ}

lemma lemma_1 (hp : 2 ≤ p) (hpeven : even p) (f : G → ℝ≥0) (B₁ B₂ A : finset G) :
  ∃ (A₁ ⊆ B₁) (A₂ ⊆ B₂), ⟪μ_[ℝ] A₁ ○ μ A₂, coe ∘ f⟫_[ℝ] ≤
    2 * (∑ x, (μ B₁ ○ μ B₂) x * (𝟭 A ○ 𝟭 A) x ^ p * f x) / ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ p
    ∧ (4 : ℝ)⁻¹ * A.card ^ (-2 * p : ℤ) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p)
      ≤ A₁.card / B₁.card
    ∧ (4 : ℝ)⁻¹ * A.card ^ (-2 * p : ℤ) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p)
      ≤ A₂.card / B₂.card :=
begin
  sorry
end

noncomputable def S (p : ℝ≥0) (ε : ℝ) (B₁ B₂ A : finset G) : finset G :=
univ.filter $ λ x, (1 - ε) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] < (𝟭 A ○ 𝟭 A) x

@[simp] lemma mem_S {p : ℝ≥0} {ε : ℝ} {B₁ B₂ A : finset G} {x : G} :
  x ∈ S p ε B₁ B₂ A ↔ (1 - ε) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] < (𝟭 A ○ 𝟭 A) x :=
by simp [S]

lemma lemma_2 (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hp : even p) (hp₂ : 2 ≤ p)
  (hpε : ε⁻¹ * log (2 / δ) ≤ p) (hB : (B₁ ∩ B₂).nonempty) {hA : A.nonempty} :
  ∃ (A₁ ⊆ B₁) (A₂ ⊆ B₂), 1 - δ ≤ ∑ x in S p ε B₁ B₂ A, (μ A₁ ○ μ A₂) x ∧
    (4 : ℝ)⁻¹ * A.card ^ (-2 * p : ℤ) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) ≤
      A₁.card / B₁.card ∧
    (4 : ℝ)⁻¹ * A.card ^ (-2 * p : ℤ) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) ≤
      A₂.card / B₂.card :=
begin
  obtain ⟨A₁, hAB₁, A₂, hAB₂, h, hcard₁, hcard₂⟩ := lemma_1 hp₂ hp (𝟭 (S p ε B₁ B₂ A)ᶜ) B₁ B₂ A,
  refine ⟨A₁, hAB₁, A₂, hAB₂, _, hcard₁, hcard₂⟩,
  have : 0 < ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ p,
  { rw wLpnorm_pow_eq_sum,
    refine sum_pos' (λ x _, smul_nonneg zero_le' $ hp.pow_nonneg _) ⟨0, mem_univ _,
      smul_pos _ $ hp.pow_pos _⟩,
    { refine lt_of_le_of_ne' (dconv_nonneg mu_nonneg mu_nonneg _) _,
      rwa [←function.mem_support, support_dconv, support_mu, support_mu, ←coe_sub, mem_coe,
        zero_mem_sub_iff, not_disjoint_iff_nonempty_inter]; exact mu_nonneg },
    { rw [norm_ne_zero_iff, ←function.mem_support, support_dconv, support_indicator],
      exact hA.to_set.zero_mem_sub,
      all_goals { positivity } },
    { positivity } },
  have aux : ∀ (C : finset G) r,
    (4 : ℝ)⁻¹ * A.card ^ (-2 * p : ℤ) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) ≤
      C.card / r → C.nonempty,
  { simp_rw nonempty_iff_ne_empty,
    rintro C r h rfl,
    simp [pow_mul', (zero_lt_four' ℝ).not_le, inv_mul_le_iff (zero_lt_four' ℝ), mul_assoc,
      mul_nonpos_iff, (pow_pos this 2).not_le] at h,
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
        : by simp [L2inner_eq_sum, -mem_compl, -mem_S, apply_ite coe]
    ... ≤ _ : h
    ... ≤ _ : _,
  { simp_rw [sub_eq_iff_eq_add', sum_add_sum_compl, sum_dconv, map_mu],
    rw [sum_mu _ hA₁, sum_mu _ hA₂, one_mul]; apply_instance },
  rw [div_le_iff this, ←le_div_iff' (zero_lt_two' ℝ), mul_div_right_comm],
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
