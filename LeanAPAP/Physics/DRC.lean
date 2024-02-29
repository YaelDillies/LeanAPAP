import LeanAPAP.Mathlib.Algebra.BigOperators.Ring
import LeanAPAP.Mathlib.Data.Real.Sqrt
import LeanAPAP.Prereqs.Discrete.Convolution.Norm
import LeanAPAP.Prereqs.Discrete.LpNorm.Weighted

/-!
# Dependent Random Choice
-/

open Real Finset Fintype Function
open scoped BigOps NNReal Pointwise

variable {G : Type*} [DecidableEq G] [Fintype G] [AddCommGroup G] {p : ℕ} {B₁ B₂ A : Finset G}
  {ε δ : ℝ}

/-- Auxiliary definition for the Dependent Random Choice step. We intersect `B₁` and `B₂` with
`c p A s` for some `s`. -/
private def c (p : ℕ) (A : Finset G) (s : Fin p → G) : Finset G := univ.inf fun i ↦ s i +ᵥ A

private lemma lemma_0 (p : ℕ) (B₁ B₂ A : Finset G) (f : G → ℝ) :
    ∑ s, ⟪𝟭_[ℝ] (B₁ ∩ c p A s) ○ 𝟭 (B₂ ∩ c p A s), f⟫_[ℝ] =
      (B₁.card * B₂.card) • ∑ x, (μ_[ℝ] B₁ ○ μ B₂) x * (𝟭 A ○ 𝟭 A) x ^ p * f x := sorry

private lemma sum_c (p : ℕ) (B A : Finset G) : ∑ s, (B ∩ c p A s).card = A.card ^ p * B.card := by
  sorry

private lemma sum_cast_c (p : ℕ) (B A : Finset G) :
    ∑ s, ((B ∩ c p A s).card : ℝ) = A.card ^ p * B.card := sorry

/-- If `A` is nonempty, and `B₁` and `B₂` intersect, then the `μ B₁ ○ μ B₂`-weighted Lp norm of
`𝟭 A ○ 𝟭 A` is positive. -/
private lemma lpNorm_conv_pos (hp : p ≠ 0) (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty) :
    0 < ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ p := sorry

lemma drc (hp₂ : 2 ≤ p) (f : G → ℝ≥0) (hf : ∃ x, x ∈ B₁ - B₂ ∧ x ∈ A - A ∧ x ∈ f.support)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty) :
    ∃ A₁, A₁ ⊆ B₁ ∧ ∃ A₂, A₂ ⊆ B₂ ∧
      ⟪μ_[ℝ] A₁ ○ μ A₂, (↑) ∘ f⟫_[ℝ] * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ p
        ≤ 2 * ∑ x, (μ B₁ ○ μ B₂) x * (𝟭_[ℝ] A ○ 𝟭 A) x ^ p * f x ∧
      (4 : ℝ) ⁻¹ * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) / A.card ^ (2 * p)
        ≤ A₁.card / B₁.card ∧
      (4 : ℝ) ⁻¹ * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) / A.card ^ (2 * p)
        ≤ A₂.card / B₂.card := by
  have hp₀ : p ≠ 0 := by positivity
  have := lpNorm_conv_pos hp₀ hB hA
  set M : ℝ :=
    2 ⁻¹ * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ p * (sqrt B₁.card * sqrt B₂.card) / A.card ^ p
      with hM_def
  have hM : 0 < M := by rw [hM_def]; positivity
  set A₁ := fun s ↦ B₁ ∩ c p A s
  set A₂ := fun s ↦ B₂ ∩ c p A s
  set g : (Fin p → G) → ℝ := fun s ↦ (A₁ s).card * (A₂ s).card with hg_def
  have hg : ∀ s, 0 ≤ g s := fun s ↦ by rw [hg_def]; dsimp; positivity
  suffices ∑ s, ⟪𝟭_[ℝ] (A₁ s) ○ 𝟭 (A₂ s), (↑) ∘ f⟫_[ℝ] * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ p
    < ∑ s, 𝟭 (univ.filter fun s ↦ M ^ 2 ≤ g s) s * g s *
        (2 * ∑ x, (μ B₁ ○ μ B₂) x * (𝟭_[ℝ] A ○ 𝟭 A) x ^ p * f x) by
    obtain ⟨s, -, hs⟩ := exists_lt_of_sum_lt this
    refine ⟨_, inter_subset_left _ $ c p A s, _, inter_subset_left _ $ c p A s, ?_⟩
    simp only [indicate_apply, mem_filter, mem_univ, true_and_iff, boole_mul] at hs
    split_ifs at hs with h; swap
    · sorry
    have : (4 : ℝ) ⁻¹ * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) / A.card ^ (2 * p)
      ≤ (A₁ s).card / B₁.card * ((A₂ s).card / B₂.card) := by
      rw [div_mul_div_comm, le_div_iff]
      simpa [hg_def, hM_def, mul_pow, pow_mul', show (2 : ℝ) ^ 2 = 4 by norm_num,
        mul_div_right_comm] using h
      positivity
    refine ⟨sorry, sorry, this.trans $ mul_le_of_le_one_left ?_ sorry⟩
    positivity -- FIXME: Why is this timing out?
  sorry

#exit

noncomputable def s (p : ℝ≥0) (ε : ℝ) (B₁ B₂ A : Finset G) : Finset G :=
  univ.filter fun x ↦ (1 - ε) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] < (𝟭 A ○ 𝟭 A) x

@[simp]
lemma mem_s {p : ℝ≥0} {ε : ℝ} {B₁ B₂ A : Finset G} {x : G} :
    x ∈ s p ε B₁ B₂ A ↔ (1 - ε) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] < (𝟭 A ○ 𝟭 A) x := by simp [s]

--TODO: When `1 < ε`, the result is trivial since `S = univ`.
lemma sifting (B₁ B₂ : Finset G) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hp : Even p)
    (hp₂ : 2 ≤ p) (hpε : ε⁻¹ * log (2 / δ) ≤ p) (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty)
    (hf : ∃ x, x ∈ B₁ - B₂ ∧ x ∈ A - A ∧ x ∉ s p ε B₁ B₂ A) :
    ∃ A₁, A₁ ⊆ B₁ ∧ ∃ A₂, A₂ ⊆ B₂ ∧ 1 - δ ≤ ∑ x in s p ε B₁ B₂ A, (μ A₁ ○ μ A₂) x ∧
        (4 : ℝ)⁻¹ * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) / A.card ^ (2 * p) ≤
            A₁.card / B₁.card ∧
          (4 : ℝ)⁻¹ * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) / A.card ^ (2 * p) ≤
            A₂.card / B₂.card := by
  obtain ⟨A₁, hAB₁, A₂, hAB₂, h, hcard₁, hcard₂⟩ :=
    drc hp₂ (𝟭 (s p ε B₁ B₂ A)ᶜ)
      (by simpa only [support_indicate, coe_compl, Set.mem_compl_iff, mem_coe]) hB hA
  refine ⟨A₁, hAB₁, A₂, hAB₂, ?_, hcard₁, hcard₂⟩
  have hp₀ : 0 < p := by positivity
  have aux :
    ∀ (c : Finset G) (r),
      (4 : ℝ)⁻¹ * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ (2 * p) / A.card ^ (2 * p) ≤ c.card / r →
        c.Nonempty := by
    simp_rw [nonempty_iff_ne_empty]
    rintro c r h rfl
    simp [pow_mul', (zero_lt_four' ℝ).not_le, inv_mul_le_iff (zero_lt_four' ℝ), mul_assoc,
      div_nonpos_iff, mul_nonpos_iff, (pow_pos (lpNorm_conv_pos hp₀.ne' hB hA) 2).not_le] at h
    norm_cast at h
    simp [hp₀, hA.ne_empty] at h
  have hA₁ : A₁.Nonempty := aux _ _ hcard₁
  have hA₂ : A₂.Nonempty := aux _ _ hcard₂
  clear hcard₁ hcard₂ aux
  rw [sub_le_comm]
  calc
    _ = ∑ x in (s p ε B₁ B₂ A)ᶜ, (μ A₁ ○ μ A₂) x := ?_
    _ = ⟪μ_[ℝ] A₁ ○ μ A₂, (↑) ∘ 𝟭_[ℝ≥0] ((s (↑p) ε B₁ B₂ A)ᶜ)⟫_[ℝ] := by
      simp [l2Inner_eq_sum, -mem_compl, -mem_s, apply_ite NNReal.toReal, indicate_apply]
    _ ≤ _ := (le_div_iff $ lpNorm_conv_pos hp₀.ne' hB hA).2 h
    _ ≤ _ := ?_
  · simp_rw [sub_eq_iff_eq_add', sum_add_sum_compl, sum_dconv, map_mu]
    rw [sum_mu _ hA₁, sum_mu _ hA₂, one_mul]
  rw [div_le_iff (lpNorm_conv_pos hp₀.ne' hB hA), ←le_div_iff' (zero_lt_two' ℝ)]
  simp only [apply_ite NNReal.toReal, indicate_apply, NNReal.coe_one, NNReal.coe_zero, mul_boole,
    sum_ite_mem, univ_inter, mul_div_right_comm]
  calc
    ∑ x in (s p ε B₁ B₂ A)ᶜ, (μ B₁ ○ μ B₂) x * (𝟭 A ○ 𝟭 A) x ^ p ≤
        ∑ x in (s p ε B₁ B₂ A)ᶜ,
          (μ B₁ ○ μ B₂) x * ((1 - ε) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂]) ^ p :=
      sum_le_sum fun x hx ↦ mul_le_mul_of_nonneg_left (pow_le_pow_left
        (dconv_nonneg indicate_nonneg indicate_nonneg _) (by simpa using hx) _)
          (dconv_nonneg mu_nonneg mu_nonneg _)
    _ ≤ ∑ x, (μ B₁ ○ μ B₂) x * ((1 - ε) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂]) ^ p :=
      (sum_le_univ_sum_of_nonneg fun x ↦
        mul_nonneg (dconv_nonneg mu_nonneg mu_nonneg _) $ hp.pow_nonneg _)
    _ = ‖μ_[ℝ] B₁‖_[1] * ‖μ_[ℝ] B₂‖_[1] * ((1 - ε) ^ p * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ B₁ ○ μ B₂] ^ p)
        := ?_
    _ ≤ _ :=
      (mul_le_of_le_one_left (mul_nonneg (hp.pow_nonneg _) $ hp.pow_nonneg _) $
        mul_le_one l1Norm_mu_le_one lpNorm_nonneg l1Norm_mu_le_one)
    _ ≤ _ := mul_le_mul_of_nonneg_right ?_ $ hp.pow_nonneg _
  · have : 0 ≤ μ_[ℝ] B₁ ○ μ B₂ := dconv_nonneg mu_nonneg mu_nonneg
    simp_rw [←l1Norm_dconv mu_nonneg mu_nonneg, l1Norm_eq_sum, norm_of_nonneg (this _), sum_mul,
      mul_pow]
  calc
    (1 - ε) ^ p ≤ exp (-ε) ^ p := pow_le_pow_left (sub_nonneg.2 hε₁) (one_sub_le_exp_neg _) _
    _ = exp (-(ε * p)) := by rw [←neg_mul, exp_mul, rpow_nat_cast]
    _ ≤ exp (-log (2 / δ)) :=
      (exp_monotone $ neg_le_neg $ (inv_mul_le_iff $ by positivity).1 hpε)
    _ = δ / 2 := by rw [exp_neg, exp_log, inv_div]; positivity

--TODO: When `1 < ε`, the result is trivial since `S = univ`.
/-- Special case of `sifting` when `B₁ = B₂ = univ`. -/
lemma sifting_cor (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hp : Even p) (hp₂ : 2 ≤ p)
    (hpε : ε⁻¹ * log (2 / δ) ≤ p) (hA : A.Nonempty)
    (hf : ∃ x, x ∈ A - A ∧ (𝟭 A ○ 𝟭 A) x ≤ (1 - ε) * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ univ]) :
    ∃ A₁ A₂, 1 - δ ≤ ∑ x in s p ε univ univ A, (μ A₁ ○ μ A₂) x ∧
        (4 : ℝ)⁻¹ * (A.card / card G : ℝ) ^ (2 * p) ≤ A₁.card / card G ∧
          (4 : ℝ)⁻¹ * (A.card / card G : ℝ) ^ (2 * p) ≤ A₂.card / card G := by
  have hp₀ : p ≠ 0 := by positivity
  have :
    (4 : ℝ)⁻¹ * (A.card / card G) ^ (2 * p) ≤
      4⁻¹ * ‖𝟭_[ℝ] A ○ 𝟭 A‖_[p, μ univ] ^ (2 * p) / A.card ^ (2 * p) := by
    rw [mul_div_assoc, ←div_pow]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left (by positivity) ?_ _) (by norm_num)
    rw [le_div_iff, ←mul_div_right_comm]
    calc
      _ = ‖𝟭_[ℝ] A ○ 𝟭 A‖_[1, μ univ] := by
        simp [mu, wlpNorm_smul_right, hp₀, l1Norm_dconv, card_univ, inv_mul_eq_div]
      _ ≤ _ := wlpNorm_mono_right (one_le_two.trans $ by norm_cast) _ _
    · exact Nat.cast_pos.2 hA.card_pos
  obtain ⟨A₁, -, A₂, -, h, hcard₁, hcard₂⟩ :=
    sifting univ univ hε hε₁ hδ hp hp₂ hpε (by simp [univ_nonempty]) hA (by simpa)
  exact ⟨A₁, A₂, h, this.trans $ by simpa using hcard₁, this.trans $ by simpa using hcard₂⟩
