import analysis.inner_product_space.pi_L2
import analysis.special_functions.log.basic
import analysis.special_functions.pow.real
import mathlib.analysis.normed.group.basic
import mathlib.analysis.normed_space.pi_Lp
import mathlib.analysis.normed_space.ray
import mathlib.analysis.special_functions.log.basic

/-!
# Miscellaneous definitions
-/

open set
open_locale big_operators complex_conjugate ennreal nnreal

/-! ### Translation operator -/

section translate
variables {ι α β γ : Type*} [fintype ι] [add_comm_group α]

def translate (a : α) (f : α → β) : α → β := λ x, f (x - a)

notation `τ ` := translate

@[simp] lemma translate_apply (a : α) (f : α → β) (x : α) : τ a f x = f (x - a) := rfl

@[simp] lemma translate_zero (f : α → β) : translate 0 f = f := by ext; simp

@[simp] lemma translate_translate (a b : α) (f : α → β) : τ a (τ b f) = τ (a + b) f :=
by ext; simp [sub_sub]

@[simp] lemma comp_translate (a : α) (f : α → β) (g : β → γ) : g ∘ τ a f = τ a (g ∘ f) := rfl

variables [add_comm_group β]

@[simp] lemma translate_zero_right (a : α) : τ a (0 : α → β) = 0 := rfl
lemma translate_add_right (a : α) (f g : α → β) : τ a (f + g) = τ a f + τ a g := rfl
lemma translate_sub_right (a : α) (f g : α → β) : τ a (f - g) = τ a f - τ a g := rfl
lemma translate_neg_right (a : α) (f : α → β) : τ a (-f) = -τ a f := rfl
lemma translate_sum_right (a : α) (f : ι → α → β) : τ a (∑ i, f i) = ∑ i, τ a (f i) := by ext; simp
@[simp] lemma translate_smul_right [has_smul γ β] [add_comm_group α] (a : α) (f : α → β) (c : γ) :
  τ a (c • f) = c • τ a f := rfl

end translate

/-! ### Conjugation negation operator -/

section conjneg
variables {ι α β γ : Type*} [fintype ι] [add_comm_group α]

section comm_semiring
variables [comm_semiring β] [star_ring β]

def conjneg (f : α → β) : α → β := λ x, conj (f (-x))

@[simp] lemma conjneg_apply (f : α → β) (x : α) : conjneg f x = conj (f (-x)) := rfl
@[simp] lemma conjneg_conjneg (f : α → β) : conjneg (conjneg f) = f := by ext; simp
@[simp] lemma conjneg_zero : conjneg (0 : α → β) = 0 := by ext; simp
@[simp] lemma conjneg_add (f g : α → β) : conjneg (f + g) = conjneg f + conjneg g := by ext; simp
@[simp] lemma conjneg_sum (f : ι → α → β) : conjneg (∑ i, f i) = ∑ i, conjneg (f i) :=
by ext; simp only [map_sum, conjneg_apply, fintype.sum_apply]
@[simp] lemma conjneg_prod (f : ι → α → β) : conjneg (∏ i, f i) = ∏ i, conjneg (f i) :=
by ext; simp only [map_prod, conjneg_apply, fintype.prod_apply]

end comm_semiring

section comm_ring
variables [comm_ring β] [star_ring β]

@[simp] lemma conjneg_sub (f g : α → β) : conjneg (f - g) = conjneg f - conjneg g := by ext; simp
@[simp] lemma conjneg_neg (f : α → β) : conjneg (-f) = -conjneg f := by ext; simp

end comm_ring
end conjneg

namespace real
variables {x : ℝ}

-- Maybe define as `2 - log x`
noncomputable def curlog (x : ℝ) : ℝ := log (exp 2 / x)

@[simp] lemma curlog_zero : curlog 0 = 0 := by simp [curlog]

lemma two_le_curlog (hx₀ : 0 < x) (hx : x ≤ 1) : 2 ≤ x.curlog :=
(le_log_iff_exp_le (by positivity)).2 (le_div_self (exp_pos _).le hx₀ hx)

lemma curlog_pos (hx₀ : 0 < x) (hx : x ≤ 1) : 0 < x.curlog :=
zero_lt_two.trans_le $ two_le_curlog hx₀ hx

lemma curlog_nonneg (hx₀ : 0 ≤ x) (hx : x ≤ 1) : 0 ≤ x.curlog :=
begin
  obtain rfl | hx₀ := hx₀.eq_or_lt,
  { simp },
  { exact (curlog_pos hx₀ hx).le }
end

-- Might work with x = 0
lemma log_one_div_le_curlog (hx : 0 < x) : log (1 / x) ≤ curlog x :=
log_le_log_of_le (by positivity) (div_le_div_of_le hx.le (one_le_exp two_pos.le))

-- Might work with x = 0
lemma log_inv_le_curlog (hx : 0 < x) : log (x⁻¹) ≤ curlog x :=
by { rw ←one_div, exact log_one_div_le_curlog hx }

-- This might work with x = 1, not sure
lemma pow_neg_one_div_curlog (hx : 0 ≤ x) (hx' : x < 1) : x ^ (- 1 / curlog x) ≤ exp 1 :=
begin
  obtain rfl | hx := hx.eq_or_lt,
  { simp },
  have : -1 / log (1 / x) ≤ -1 / curlog x,
  { rw [neg_div, neg_div, neg_le_neg_iff],
    refine one_div_le_one_div_of_le _ (log_one_div_le_curlog hx),
    refine log_pos _,
    rwa [lt_div_iff hx, one_mul] },
  refine (rpow_le_rpow_of_exponent_ge hx hx'.le this).trans _,
  rw [one_div, log_inv, rpow_def_of_pos hx, neg_div_neg_eq, mul_one_div, div_self],
  exact log_ne_zero_of_pos_of_ne_one hx hx'.ne
end

end real

/-! ### Norms -/

section Lpnorm
variables {ι : Type*} [fintype ι] {α : ι → Type*} [Π i, normed_add_comm_group (α i)] {p : ℝ≥0∞}

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

section one_le
variables {f g h : Π i, α i}

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

/-! ### Wide diagonal -/

namespace finset
variables {α : Type*} [decidable_eq α] {k : ℕ}

def wide_diag (k : ℕ) (s : finset α) : finset (fin k → α) := s.image (λ i _, i)

def _root_.fintype_wide_diag [fintype α] (k : ℕ) : finset (fin k → α) := univ.wide_diag k

@[simp] lemma card_wide_diag (hk : k ≠ 0) (s : finset α) : (s.wide_diag k).card = s.card :=
begin
  cases k,
  { cases hk rfl },
  rw [finset.wide_diag, card_image_of_injective],
  exact λ i j h, congr_fun h 0,
end

end finset
