import analysis.special_functions.pow.real
import mathlib.analysis.special_functions.log.basic

/-!
# Miscellaneous definitions
-/

open set
open_locale complex_conjugate

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

namespace finset

/-! ### Wide diagonal -/

variables {α : Type*} [decidable_eq α] {k : ℕ}

def wide_diag (k : ℕ) (s : finset α) : finset (fin k → α) := s.image (λ i _, i)

lemma mem_wide_diag {s : finset α} {k : ℕ} {x : fin k → α} :
  x ∈ s.wide_diag k ↔ ∃ i ∈ s, (λ _, i) = x := mem_image

def _root_.fintype_wide_diag (α : Type*) [decidable_eq α] [fintype α] (k : ℕ) :
  finset (fin k → α) := univ.wide_diag k

lemma mem_fintype_wide_diag [fintype α] {k : ℕ} {x : fin k → α} :
  x ∈ fintype_wide_diag α k ↔ ∃ i, (λ _, i) = x :=
mem_wide_diag.trans (by simp)

@[simp] lemma card_wide_diag (hk : k ≠ 0) (s : finset α) : (s.wide_diag k).card = s.card :=
begin
  cases k,
  { cases hk rfl },
  rw [finset.wide_diag, card_image_of_injective],
  exact λ i j h, congr_fun h 0,
end

open_locale big_operators

/-! ### a finset thing that should actually be called pow_sum and the other thing should be called sum_pow because the binary version of that is called add_pow and the binary version of this is called pow_add -/
lemma pow_sum_but_its_actually_pow_sum
  {α β : Type*} [comm_monoid β] (s : finset α) (f : α → ℕ) (m : β) :
  ∏ i in s, m ^ f i = m ^ (∑ i in s, f i) :=
begin
  induction s using finset.cons_induction_on with a s has ih,
  { simp },
  rw [prod_cons, ih, sum_cons, pow_add],
end

/-! # some nice things -/
lemma sum_nbij {α β γ : Type*} [add_comm_monoid β] {s : finset α} {t : finset γ}
  {f : α → β} {g : γ → β} (i : α → γ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
  (i_inj : ∀ a₁ a₂, a₁ ∈ s → a₂ ∈ s → i a₁ = i a₂ → a₁ = a₂) (i_surj : ∀ b ∈ t, ∃ a ∈ s, b = i a) :
  (∑ x in s, f x) = (∑ x in t, g x) :=
sum_bij (λ a _, i a) hi h i_inj i_surj

lemma sum_nbij' {α β γ : Type*} [add_comm_monoid β] {s : finset α} {t : finset γ}
  {f : α → β} {g : γ → β}
  (i : α → γ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
  (j : γ → α) (hj : ∀ a ∈ t, j a ∈ s) (left_inv : ∀ a ∈ s, j (i a) = a)
  (right_inv : ∀ a ∈ t, i (j a) = a) :
  (∑ x in s, f x) = (∑ x in t, g x) :=
sum_bij' (λ a _, i a) hi h (λ b _, j b) hj left_inv right_inv

end finset
