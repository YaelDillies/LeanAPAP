import analysis.special_functions.pow.real
import mathlib.analysis.special_functions.log.basic

/-!
# Miscellaneous definitions
-/

open set
open_locale complex_conjugate nnreal

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

lemma log_one_div_le_curlog (hx : 0 ≤ x) : log (1 / x) ≤ curlog x :=
begin
  rcases hx.eq_or_lt with rfl | hx,
  { simp },
  exact log_le_log_of_le (by positivity) (div_le_div_of_le hx.le (one_le_exp two_pos.le))
end

lemma log_inv_le_curlog (hx : 0 ≤ x) : log (x⁻¹) ≤ curlog x :=
by { rw ←one_div, exact log_one_div_le_curlog hx }

-- This might work with x = 1, not sure
lemma pow_neg_one_div_curlog (hx : 0 ≤ x) (hx' : x < 1) : x ^ (- 1 / curlog x) ≤ exp 1 :=
begin
  obtain rfl | hx := hx.eq_or_lt,
  { simp },
  have : -1 / log (1 / x) ≤ -1 / curlog x,
  { rw [neg_div, neg_div, neg_le_neg_iff],
    refine one_div_le_one_div_of_le _ (log_one_div_le_curlog hx.le),
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

end finset

/-! ### Normalised indicator -/

section division_semiring
variables {α β : Type*} [division_semiring β] [decidable_eq α] {s : finset α}

def indicator (s : finset α) (a : α) : β := ite (a ∈ s) 1 0

notation `𝟭 ` := _root_.indicator

notation `𝟭_[` β `] ` := @_root_.indicator _ β _ _

@[simp] lemma indicator_apply (x : α) : 𝟭_[β] s x = ite (x ∈ s) 1 0 := rfl

/-- The normalised indicator of a set. -/
def mu (s : finset α) : α → β := (s.card : β)⁻¹ • λ x, ite (x ∈ s) 1 0

notation `μ ` := _root_.mu

notation `μ_[` β `] ` := @_root_.mu _ β _ _

lemma mu_apply (x : α) : μ s x = (s.card : β)⁻¹ * ite (x ∈ s) 1 0 := rfl

@[simp] lemma mu_empty : (μ ∅ : α → β) = 0 := by ext; simp [mu]

lemma smul_mu [char_zero β] : s.card • μ_[β] s = 𝟭 s :=
begin
  ext x : 1,
  rw [pi.smul_apply, mu_apply, nsmul_eq_mul],
  split_ifs,
  { rw [mul_one, mul_inv_cancel],
    rw [nat.cast_ne_zero, ←pos_iff_ne_zero, finset.card_pos],
    exact ⟨_, h⟩ },
  { rw [mul_zero, mul_zero] }
end

end division_semiring

section linear_ordered_field
variables {α β : Type*} [linear_ordered_field β] [decidable_eq α] {s : finset α}

lemma indicator_nonneg : 0 ≤ 𝟭_[β] s := λ a, by rw _root_.indicator_apply; split_ifs; norm_num

lemma mu_nonneg : 0 ≤ μ_[β] s := λ a, by rw mu_apply; split_ifs; norm_num

end linear_ordered_field
