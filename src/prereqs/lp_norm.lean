import analysis.inner_product_space.pi_L2
import mathlib.analysis.normed.group.basic
import mathlib.analysis.normed_space.pi_Lp
import mathlib.analysis.normed_space.ray
import mathlib.analysis.special_functions.log.basic
import mathlib.analysis.special_functions.pow.real
import prereqs.misc
import prereqs.translate

/-!
# Lp norm
-/

open set
open_locale big_operators complex_conjugate ennreal nnreal

section Lpnorm
variables {ι : Type*} [fintype ι] {α : ι → Type*} [Π i, normed_add_comm_group (α i)] {p : ℝ≥0∞}
  {f g h : Π i, α i}

/-- The Lp norm of a function. -/
@[reducible] noncomputable def Lpnorm (p : ℝ≥0∞) (f : Π i, α i) : ℝ :=
‖(pi_Lp.equiv p _).symm f‖

notation `‖` f `‖_[` p `]` := Lpnorm p f

lemma Lpnorm_eq_sum' (hp : 0 < p.to_real) (f : Π i, α i) :
  ‖f‖_[p] = (∑ i, ‖f i‖ ^ p.to_real) ^ p.to_real⁻¹ :=
by rw ←one_div; exact pi_Lp.norm_eq_sum hp _

lemma Lpnorm_eq_sum'' {p : ℝ} (hp : 0 < p) (f : Π i, α i) :
  ‖f‖_[p.to_nnreal] = (∑ i, ‖f i‖ ^ p) ^ p⁻¹ :=
by rw [Lpnorm_eq_sum']; simp [hp, hp.le]

lemma Lpnorm_eq_sum {p : ℝ≥0} (hp : 0 < p) (f : Π i, α i) :
  ‖f‖_[p] = (∑ i, ‖f i‖ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) :=
Lpnorm_eq_sum' hp _

lemma Lpnorm_rpow_eq_sum {p : ℝ≥0} (hp : 0 < p) (f : Π i, α i) :
  ‖f‖_[p] ^ (p : ℝ) = ∑ i, ‖f i‖ ^ (p : ℝ) :=
begin
  rw [Lpnorm_eq_sum hp, real.rpow_inv_rpow],
  { exact finset.sum_nonneg (λ i _, by positivity) },
  { positivity }
end

lemma L1norm_eq_sum (f : Π i, α i) : ‖f‖_[1] = ∑ i, ‖f i‖ := by simp [Lpnorm_eq_sum']

lemma L0norm_eq_card (f : Π i, α i) : ‖f‖_[0] = {i | f i ≠ 0}.to_finite.to_finset.card :=
pi_Lp.norm_eq_card _

lemma Linftynorm_eq_csupr (f : Π i, α i) : ‖f‖_[∞] = ⨆ i, ‖f i‖ := pi_Lp.norm_eq_csupr _

@[simp] lemma Lpnorm_zero : ‖(0 : Π i, α i)‖_[p] = 0 :=
begin
  cases p, swap,
  obtain rfl | hp := @eq_zero_or_pos _ _ p,
  all_goals { simp [Linftynorm_eq_csupr, L0norm_eq_card, Lpnorm_eq_sum, *, ne_of_gt] },
end

@[simp] lemma Lpnorm_nonneg : 0 ≤ ‖f‖_[p] :=
begin
  cases p,
  { simp only [Linftynorm_eq_csupr, ennreal.none_eq_top],
    exact real.supr_nonneg (λ i, norm_nonneg _) },
  obtain rfl | hp := @eq_zero_or_pos _ _ p,
  { simp only [L0norm_eq_card, ennreal.some_eq_coe, ennreal.coe_zero],
    exact nat.cast_nonneg _ },
  { simp only [Lpnorm_eq_sum hp, ennreal.some_eq_coe],
    exact real.rpow_nonneg_of_nonneg
      (finset.sum_nonneg $ λ i _, real.rpow_nonneg_of_nonneg (norm_nonneg _) _) _ }
end

section one_le

-- TODO: Remove the `1 ≤ p` condition
lemma Lpnorm_sub_comm (hp : 1 ≤ p) (f g : Π i, α i) : ‖f - g‖_[p] = ‖g - f‖_[p] :=
by haveI := fact.mk hp; exact norm_sub_rev _ _

lemma Lpnorm_add_le (hp : 1 ≤ p) (f g : Π i, α i) : ‖f + g‖_[p] ≤ ‖f‖_[p] + ‖g‖_[p] :=
by haveI := fact.mk hp; exact norm_add_le _ _

lemma Lpnorm_sub_le (hp : 1 ≤ p) (f g : Π i, α i) : ‖f - g‖_[p] ≤ ‖f‖_[p] + ‖g‖_[p] :=
by haveI := fact.mk hp; exact norm_sub_le _ _

lemma Lpnorm_sub_le_Lpnorm_sub_add_Lpnorm_sub (hp : 1 ≤ p) :
  ‖f - h‖_[p] ≤ ‖f - g‖_[p] + ‖g - h‖_[p] :=
by haveI := fact.mk hp; exact norm_sub_le_norm_sub_add_norm_sub

variables {𝕜 : Type*} [normed_field 𝕜] [Π i, normed_space 𝕜 (α i)]

-- TODO: `p ≠ 0` is enough
lemma Lpnorm_smul (hp : 1 ≤ p) (c : 𝕜) (f : Π i, α i) : ‖c • f‖_[p] = ‖c‖ * ‖f‖_[p] :=
by haveI := fact.mk hp; exact norm_smul _ _

-- TODO: Why is it so hard to use `Lpnorm_smul` directly? `function.has_smul` seems to have a hard
-- time unifying `pi.has_smul`
lemma Lpnorm_smul' {α : Type*} [normed_add_comm_group α] [normed_space 𝕜 α] (hp : 1 ≤ p) (c : 𝕜)
  (f : ι → α) : ‖c • f‖_[p] = ‖c‖ * ‖f‖_[p] :=
Lpnorm_smul hp _ _

variables [Π i, normed_space ℝ (α i)]

lemma Lpnorm_nsmul (hp : 1 ≤ p) (n : ℕ) (f : Π i, α i) : ‖n • f‖_[p] = n • ‖f‖_[p] :=
by haveI := fact.mk hp; exact norm_nsmul _ _

-- TODO: Why is it so hard to use `Lpnorm_nsmul` directly? `function.has_smul` seems to have a hard
-- time unifying `pi.has_smul`
lemma Lpnorm_nsmul' {α : Type*} [normed_add_comm_group α] [normed_space ℝ α] (hp : 1 ≤ p) (n : ℕ)
  (f : ι → α) : ‖n • f‖_[p] = n • ‖f‖_[p] :=
Lpnorm_nsmul hp _ _

end one_le

/-! #### Weighted Lp norm -/

/-- The Lp norm of a function. -/
@[reducible] noncomputable def weight_Lpnorm (p : ℝ≥0) (f : Π i, α i) (w : ι → ℝ≥0) : ℝ :=
‖(λ i, w i ^ (p⁻¹ : ℝ) • ‖f i‖)‖_[p]

notation `‖` f `‖_[` p `, ` w `]` := weight_Lpnorm p f w

@[simp] lemma weight_Lpnorm_one (p : ℝ≥0) (f : Π i, α i) : ‖f‖_[p, 1] = ‖f‖_[p] :=
by obtain rfl | hp := @eq_zero_or_pos _ _ p; simp [weight_Lpnorm, L0norm_eq_card, Lpnorm_eq_sum, *]

/-! #### Inner product -/

variables (𝕜 : Type*) [is_R_or_C 𝕜] [Π i, inner_product_space 𝕜 (α i)]

@[reducible] noncomputable def L2inner (f g : Π i, α i) : 𝕜 :=
inner ((pi_Lp.equiv 2 _).symm f) ((pi_Lp.equiv 2 _).symm g)

notation `⟪`f`, `g`⟫_[`𝕜`]` := L2inner 𝕜 f g

lemma L2inner_eq_sum (f g : Π i, α i) : ⟪f, g⟫_[𝕜] = ∑ i, inner (f i) (g i) :=
pi_Lp.inner_apply _ _

end Lpnorm

section Lpnorm
variables {α β : Type*} [add_comm_group α] [fintype α] [normed_add_comm_group β] {p : ℝ≥0∞}

@[simp] lemma Lpnorm_translate (a : α) (f : α → β) : ‖τ a f‖_[p] = ‖f‖_[p] :=
begin
  cases p,
  { simp only [Linftynorm_eq_csupr, ennreal.none_eq_top, translate_apply],
    exact (equiv.sub_right _).supr_congr (λ _, rfl) },
  obtain rfl | hp := @eq_zero_or_pos _ _ p,
  { simp only [L0norm_eq_card, translate_apply, ne.def, ennreal.some_eq_coe, ennreal.coe_zero,
      nat.cast_inj],
    exact finset.card_congr (λ x _, x - a) (λ x hx, by simpa using hx)
      (λ x y _ _ h, by simpa using h) (λ x hx, ⟨x + a, by simpa using hx⟩) },
  { simp only [Lpnorm_eq_sum hp, ennreal.some_eq_coe, translate_apply],
    congr' 1,
    exact fintype.sum_equiv (equiv.sub_right _) _ _ (λ _, rfl) }
end

end Lpnorm

section Lpnorm
variables {ι α : Type*} [fintype α]

/-- Hölder's inequality, binary case. -/
lemma Lpnorm_mul_le (p q r : ℝ≥0∞) (hpqr : p⁻¹ + q⁻¹ = r⁻¹) (f g : α → ℂ) :
  ‖f * g‖_[r] ≤ ‖f‖_[p] * ‖g‖_[q] :=
begin
  sorry,
end

/-- Hölder's inequality, finitary case. -/
lemma Lpnorm_prod_le {s : finset ι} (p : ι → ℝ≥0∞) (q : ℝ≥0∞) (hpq : ∑ i in s, (p i)⁻¹ = q⁻¹)
  (f : ι → α → ℂ) : ‖∏ i in s, f i‖_[q] ≤ ∏ i in s, ‖f i‖_[p i] :=
begin
  classical,
  induction s using finset.induction with i s hi ih,
  sorry { simp },
  sorry
end

end Lpnorm

/-! ### Indicator -/

section mu
variables {α : Type*} [decidable_eq α] {s : finset α} {p : ℝ≥0}

noncomputable def mu (s : finset α) : α → ℂ := (s.card : ℂ)⁻¹ • λ x, ite (x ∈ s) 1 0

@[simp] lemma mu_empty : mu (∅ : finset α) = 0 := by ext; simp [mu]

variables [fintype α]

lemma Lpnorm_mu (hp : 1 ≤ p) (hs : s.nonempty) : ‖mu s‖_[p] = s.card ^ (p⁻¹ - 1 : ℝ) :=
begin
  have : (s.card : ℝ) ≠ 0 := nat.cast_ne_zero.2 hs.card_pos.ne',
  rw [mu, Lpnorm_smul'], swap,
  { exact_mod_cast hp },
  replace hp := zero_lt_one.trans_le hp,
  simp only [map_inv₀, complex.abs_cast_nat, smul_eq_mul, Lpnorm_eq_sum hp, complex.norm_eq_abs],
  have : ∀ x, (ite (x ∈ s) 1 0 : ℝ) ^ (p : ℝ) = ite (x ∈ s) (1 ^ (p : ℝ)) (0 ^ (p : ℝ)) :=
    λ x, by split_ifs; simp,
  simp_rw [apply_ite complex.abs, map_one, map_zero, this, real.zero_rpow
    (nnreal.coe_ne_zero.2 hp.ne'), real.one_rpow, finset.sum_boole, finset.filter_mem_eq_inter,
    finset.univ_inter, real.rpow_sub_one ‹_›, inv_mul_eq_div],
end

lemma Lpnorm_mu_le (hp : 1 ≤ p) : ‖mu s‖_[p] ≤ s.card ^ (p⁻¹ - 1 : ℝ) :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp,
    positivity },
  { exact (Lpnorm_mu hp hs).le }
end

lemma L1norm_mu (hs : s.nonempty) : ‖mu s‖_[1] = 1 := by simpa using Lpnorm_mu le_rfl hs

lemma L1norm_mu_le_one : ‖mu s‖_[1] ≤ 1 := by simpa using Lpnorm_mu_le le_rfl

end mu
