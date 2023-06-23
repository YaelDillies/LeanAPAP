import analysis.inner_product_space.pi_L2
import analysis.normed_space.pi_Lp
import analysis.special_functions.log.basic
import analysis.special_functions.pow.real

/-!
# Miscellaneous definitions
-/

open set
open_locale big_operators ennreal nnreal

namespace real
variables {x : ℝ}

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

-- to mathlib
lemma log_le_log_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y :=
(log_le_log hx (hx.trans_le hxy)).2 hxy

-- Might work with x = 0
lemma log_one_div_le_curlog (hx : 0 < x) : log (1 / x) ≤ curlog x :=
log_le_log_of_le (by positivity) (div_le_div_of_le hx.le (one_le_exp two_pos.le))

-- Might work with x = 0
lemma log_inv_le_curlog (hx : 0 < x) : log (x⁻¹) ≤ curlog x :=
by { rw ←one_div, exact log_one_div_le_curlog hx }

-- This might work with x = 1, not sure
lemma pow_neg_one_div_curlog (hx : 0 ≤ x) (hx' : x < 1) :
  x ^ (- 1 / curlog x) ≤ exp 1 :=
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
sorry

lemma Lpnorm_eq_sum {p : ℝ≥0} (hp : 0 < p) (f : Π i, α i) :
  ‖f‖_[p] = (∑ i, ‖f i‖ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) :=
Lpnorm_eq_sum' hp _

lemma L1norm_eq_sum (f : Π i, α i) : ‖f‖_[1] = ∑ i, ‖f i‖ := by simp [Lpnorm_eq_sum']

lemma L0norm_eq_card (f : Π i, α i) : ‖f‖_[0] = {i | f i ≠ 0}.to_finite.to_finset.card :=
pi_Lp.norm_eq_card _

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

/-! ### Indicator -/

section mu
variables {α : Type*} {s : finset α}

noncomputable def mu (s : finset α) : α → ℂ := (s.card : ℂ)⁻¹ • indicator s 1

lemma L1norm_mu [fintype α] (hs : s.nonempty) : ‖mu s‖_[1] = 1 :=
begin
  sorry
  -- simp [Lpnorm_eq_sum, zero_lt_one],
end

end mu
