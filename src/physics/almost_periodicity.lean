import algebra.order.chebyshev
import combinatorics.pigeonhole
import mathlib.data.finset.card
import prereqs.convolution
import prereqs.marcinkiewicz_zygmund
import prereqs.misc

/-!
# Almost-periodicity
-/

section
variables {α : Type*} {g : α → ℝ} {c ε : ℝ} {A : finset α}

open finset
open_locale big_operators

lemma my_markov (hc : 0 < c) (hg : ∀ a ∈ A, 0 ≤ g a) (h : ∑ a in A, g a ≤ ε * c * A.card) :
  (1 - ε) * A.card ≤ (A.filter (λ a, g a ≤ c)).card :=
begin
  rcases A.eq_empty_or_nonempty with rfl | hA,
  { simp },
  classical,
  have := h.trans' (sum_le_sum_of_subset_of_nonneg (filter_subset (λ a, ¬ g a ≤ c) A)
    (λ i hi _, hg _ hi)),
  have := (card_nsmul_le_sum _ _ c (by simp [le_of_lt] {contextual := tt})).trans this,
  rw [nsmul_eq_mul, mul_right_comm] at this,
  have := le_of_mul_le_mul_right this hc,
  rw [filter_not, cast_card_sdiff (filter_subset _ _)] at this,
  linarith only [this],
end

lemma my_other_markov (hc : 0 ≤ c) (hε : 0 ≤ ε) (hg : ∀ a ∈ A, 0 ≤ g a)
  (h : ∑ a in A, g a ≤ ε * c * A.card) : (1 - ε) * A.card ≤ (A.filter (λ a, g a ≤ c)).card :=
begin
  rcases hc.lt_or_eq with hc | rfl,
  { exact my_markov hc hg h },
  simp only [mul_zero, zero_mul] at h,
  classical,
  rw [one_sub_mul, sub_le_comm, ←cast_card_sdiff (filter_subset _ A), ←filter_not,
    filter_false_of_mem],
  { simp, positivity },
  intros i hi,
  rw (sum_eq_zero_iff_of_nonneg hg).1 (h.antisymm (sum_nonneg hg)) i hi,
  simp
end

end

section
variables {α K : Type*} {k : ℕ}

open finset

lemma card_pi_finset_fin_const (A : finset α) :
  (fintype.pi_finset (λ _ : fin k, A)).card = A.card ^ k :=
by rw [fintype.card_pi_finset, prod_const, card_univ, fintype.card_fin]

end

section
variables {G : Type*} [decidable_eq G] [add_comm_group G] {S : finset G} {k : ℕ}

open finset
open_locale big_operators pointwise

lemma big_shifts_step1 (L : finset (fin k → G)) (hk : k ≠ 0) :
  ∑ x in L + S.wide_diag k, ∑ l in L, ∑ s in S.wide_diag k, ite (l + s = x) 1 0 =
    L.card * S.card :=
begin
  simp only [@sum_comm _ _ _ _ (L + _), sum_ite_eq],
  rw sum_const_nat,
  intros l hl,
  rw [sum_const_nat, mul_one, finset.card_wide_diag hk],
  exact λ s hs, if_pos (add_mem_add hl hs),
end

variables [fintype G]

lemma reindex_count (L : finset (fin k → G)) (hk : k ≠ 0) (hL' : L.nonempty) (l₁ : fin k → G) :
    ∑ l₂ in L, ite (l₁ - l₂ ∈ fintype_wide_diag G k) 1 0 =
      (univ.filter (λ t, (l₁ - λ _, t) ∈ L)).card :=
calc
  ∑ (l₂ : fin k → G) in L, ite (l₁ - l₂ ∈ fintype_wide_diag G k) 1 0 =
    ∑ l₂ in L, ∑ t : G, ite (l₁ - (λ _, t) = l₂) 1 0 :
      begin
        refine sum_congr rfl (λ l₂ hl₂, _),
        rw fintype.sum_ite_exists,
        simp only [mem_fintype_wide_diag, @eq_comm _ l₁, eq_sub_iff_add_eq, sub_eq_iff_eq_add'],
        rintro i j h rfl,
        cases k,
        { simpa using hk },
        { simpa using congr_fun h 0 }
      end
  ... = (univ.filter (λ t, (l₁ - λ _, t) ∈ L)).card
      : by simp only [sum_comm, sum_ite_eq, card_eq_sum_ones, sum_filter]

end

variables {G : Type*} [decidable_eq G] [fintype G] [add_comm_group G] {A S : finset G} {f : G → ℂ}
  {ε : ℝ} {k m : ℕ}

open finset
open_locale big_operators pointwise nnreal ennreal

namespace almost_periodicity

def L_prop (k m : ℕ) (ε : ℝ) (f : G → ℂ) (A : finset G) (a : fin k → G) : Prop :=
‖λ x : G, ∑ i : fin k, f (x - a i) - (k • (mu A ∗ f)) x‖_[2 * m] ≤ k * ε * ‖f‖_[2 * m]

noncomputable instance : decidable_pred (L_prop k m ε f A) := classical.dec_pred _

noncomputable def L (k m : ℕ) (ε : ℝ) (f : G → ℂ) (A : finset G) : finset (fin k → G) :=
(fintype.pi_finset (λ i : fin k, A)).filter (L_prop k m ε f A)

lemma lemma28_markov (hε : 0 < ε) (hm : 1 ≤ m)
  (h : ∑ a in fintype.pi_finset (λ _, A),
    ‖λ x : G, ∑ i : fin k, f (x - a i) - (k • (mu A ∗ f)) x‖_[2 * m]^(2 * m) ≤
      1 / 2 * (k * ε * ‖f‖_[2 * m])^(2 * m) * A.card ^ k) :
  (A.card ^ k : ℝ) / 2 ≤ (L k m ε f A).card :=
begin
  rw [←nat.cast_pow, ←card_pi_finset_fin_const] at h,
  have := my_other_markov _ (by norm_num) _ h,
  rotate,
  { positivity },
  { intros a ha,
    positivity },
  norm_num1 at this,
  rw [card_pi_finset_fin_const, mul_comm, mul_one_div, nat.cast_pow] at this,
  refine this.trans_eq _,
  rw [L],
  congr' with a : 3,
  refine (@strict_mono_on_pow ℝ _ _ _).le_iff_le _ _,
  any_goals { rw set.mem_Ici },
  all_goals { positivity },
end

lemma lemma28_part_one (hm : 1 ≤ m) (x : G) :
  ∑ a in fintype.pi_finset (λ _ : fin k, A), ‖∑ i, f (x - a i) - (k • (mu A ∗ f)) x‖ ^ (2 * m) ≤
    (8 * m) ^ m * k ^ (m - 1) * ∑ a in fintype.pi_finset (λ _ : fin k, A),
      ∑ i, ‖f (x - a i) - (mu A ∗ f) x‖ ^ (2 * m) :=
begin
  let f' : G → ℂ := λ a, f (x - a) - (mu A ∗ f) x,
  refine (complex_marcinkiewicz_zygmund f' (by linarith only [hm]) _).trans_eq' _,
  { intro i,
    rw [fintype.sum_fintype_apply, sum_sub_distrib],
    simp only [f', sub_eq_zero, sum_const, indicator_apply],
    rw [←pi.smul_apply, ←smul_conv_assoc, card_smul_mu, conv_eq_sum_sub'],
    simp only [boole_mul, indicator_apply],
    rw [←sum_filter, filter_mem_eq_inter, univ_inter, sub_self, smul_zero] },
  congr' with a : 1,
  simp only [f', sum_sub_distrib, pi.smul_apply, sum_const, card_fin]
end

lemma lemma28_part_two (hm : 1 ≤ m) (hA : A.nonempty) :
  (8 * m : ℝ) ^ m * k ^ (m - 1) * ∑ a in fintype.pi_finset (λ _ : fin k, A), ∑ i : fin k,
    ‖τ (a i) f - mu A ∗ f‖_[2 * m] ^ (2 * m) ≤
  (8 * m : ℝ) ^ m * k ^ (m - 1) * ∑ a in fintype.pi_finset (λ _ : fin k, A), ∑ i : fin k,
    (2 * ‖f‖_[2 * m]) ^ (2 * m) :=
begin -- lots of the equalities about m can be automated but it's *way* slower
  have hmeq : ((2 * m : ℕ) : ℝ≥0∞) = 2 * m,
  { rw [nat.cast_mul, nat.cast_two] },
  have hm' : 1 < 2 * m,
  { refine (nat.mul_le_mul_left 2 hm).trans_lt' _,
    norm_num1 },
  have hm'' : (1 : ℝ≥0∞) ≤ 2 * m,
  { rw [←hmeq, nat.one_le_cast],
    exact hm'.le },
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  refine sum_le_sum (λ a ha, _),
  refine sum_le_sum (λ i hi, _),
  refine pow_le_pow_of_le_left (by positivity) _ _,
  refine (Lpnorm_sub_le hm'' _ _).trans _,
  rw [Lpnorm_translate, two_mul (‖f‖_[2 * m]), add_le_add_iff_left],
  have hmeq' : ((2 * m : ℝ≥0) : ℝ≥0∞) = 2 * m,
  { rw [ennreal.coe_mul, ennreal.coe_two, ennreal.coe_nat] },
  have : (1 : ℝ≥0) < 2 * m,
  { rw [←nat.cast_two, ←nat.cast_mul, nat.one_lt_cast],
    exact hm' },
  rw [←hmeq', conv_comm],
  refine (Lpnorm_conv_le this.le _ _).trans _,
  rw [L1norm_mu hA, mul_one],
end.

lemma lemma28_end (hε : 0 < ε) (hm : 1 ≤ m) (hA : A.nonempty) (hk : (64 : ℝ) * m / ε ^ 2 ≤ k) :
  (8 * m : ℝ) ^ m * k ^ (m - 1) * A.card ^ k * k * (2 * ‖f‖_[2 * m]) ^ (2 * m) ≤
    1 / 2 * ((k * ε) ^ (2 * m) * ∑ (i : G), ‖f i‖ ^ (2 * m)) * ↑(A.card) ^ k :=
begin
  have hmeq : ((2 * m : ℕ) : ℝ≥0∞) = 2 * m,
  { rw [nat.cast_mul, nat.cast_two] },
  have hm' : 2 * m ≠ 0,
  { refine mul_ne_zero two_pos.ne' _,
    rw [←pos_iff_ne_zero, ←nat.succ_le_iff],
    exact hm },
  rw [mul_pow (2 : ℝ), ←hmeq, ←Lpnorm_pow_eq_sum hm' f, ←mul_assoc, ←mul_assoc,
    mul_right_comm _ (A.card ^ k : ℝ), mul_right_comm _ (A.card ^ k : ℝ),
    mul_right_comm _ (A.card ^ k : ℝ)],
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right _ (by positivity)) (by positivity),
  rw [mul_assoc (_ ^ m : ℝ), ←pow_succ', nat.sub_add_cancel hm, pow_mul, pow_mul, ←mul_pow,
    ←mul_pow],
  have : (1 / 2 : ℝ) ^ m ≤ 1 / 2,
  { have := pow_le_pow_of_le_one (show (0 : ℝ) ≤ 1 / 2, by norm_num)
      (show (1 / 2 : ℝ) ≤ 1, by norm_num) hm,
    rwa [pow_one] at this },
  refine (mul_le_mul_of_nonneg_right this _).trans' _,
  { refine pow_nonneg _ _,
    refine sq_nonneg _ },
  rw [←mul_pow],
  refine pow_le_pow_of_le_left _ _ _,
  { positivity },
  rw [mul_right_comm, mul_comm _ ε, mul_pow, ←mul_assoc, sq (k : ℝ), ←mul_assoc],
  refine mul_le_mul_of_nonneg_right _ (nat.cast_nonneg k),
  rw [mul_right_comm, div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, le_div_iff' (zero_lt_two' ℝ),
    ←div_le_iff', ←mul_assoc],
  { norm_num1, exact hk },
  positivity
end

lemma lemma28 (hε : 0 < ε) (hm : 1 ≤ m) (hk : (64 : ℝ) * m / ε ^ 2 ≤ k) :
  (A.card ^ k : ℝ) / 2 ≤ (L k m ε f A).card :=
begin
  have : 0 < k,
  { rw ←@nat.cast_pos ℝ,
    refine hk.trans_lt' _,
    refine div_pos (mul_pos (by norm_num1) _) (pow_pos hε _),
    rw [nat.cast_pos, ←nat.succ_le_iff],
    exact hm },
  rcases A.eq_empty_or_nonempty with rfl | hA,
  { simp [zero_pow this] },
  refine lemma28_markov hε hm _,
  have hm' : 2 * m ≠ 0,
  { linarith },
  have hmeq : ((2 * m : ℕ) : ℝ≥0∞) = 2 * m,
  { rw [nat.cast_mul, nat.cast_two] },
  rw [←hmeq, mul_pow],
  simp only [Lpnorm_pow_eq_sum hm'],
  rw sum_comm,
  have : ∀ x : G,
    ∑ a in fintype.pi_finset (λ _ : fin k, A), ‖∑ i, f (x - a i) - (k • (mu A ∗ f)) x‖ ^ (2 * m) ≤
    (8 * m) ^ m * k ^ (m - 1) * ∑ a in fintype.pi_finset (λ _ : fin k, A),
      ∑ i, ‖f (x - a i) - (mu A ∗ f) x‖ ^ (2 * m),
  { exact lemma28_part_one hm },
  refine (sum_le_sum (λ x hx, this x)).trans _,
  rw ←mul_sum,
  simp only [@sum_comm _ _ G],
  have : ∀ (a : fin k → G) (i : fin k),
    ∑ x, ‖f (x - a i) - (mu A ∗ f) x‖ ^ (2 * m) = ‖τ (a i) f - mu A ∗ f‖_[2 * m] ^ (2 * m),
  { intros a i,
    rw [←hmeq, Lpnorm_pow_eq_sum hm'],
    simp only [pi.sub_apply, translate_apply] },
  simp only [this],
  have : (8 * m : ℝ) ^ m * k ^ (m - 1) * ∑ a in fintype.pi_finset (λ _ : fin k, A), ∑ i,
    ‖τ (a i) f - mu A ∗ f‖_[2 * m] ^ (2 * m) ≤
         (8 * m : ℝ) ^ m * k ^ (m - 1) * ∑ a in fintype.pi_finset (λ _ : fin k, A), ∑ i : fin k,
    (2 * ‖f‖_[2 * m]) ^ (2 * m),
  { exact lemma28_part_two hm hA },
  refine this.trans _,
  simp only [sum_const, card_fin, card_pi_finset_fin_const, nsmul_eq_mul, nat.cast_pow],
  refine (lemma28_end hε hm hA hk).trans' _,
  simp only [mul_assoc],
end

lemma just_the_triangle_inequality {t : G} {a : fin k → G} (ha : a ∈ L k m ε f A)
  (ha' : a + (λ _, t) ∈ L k m ε f A) (hk : 0 < k) (hm : 1 ≤ m) :
  ‖τ (-t) (mu A ∗ f) - mu A ∗ f‖_[2 * m] ≤ 2 * ε * ‖f‖_[2 * m] :=
begin
  let f₁ : G → ℂ := λ x, ∑ i, f (x - a i),
  let f₂ : G → ℂ := λ x, ∑ i, f (x - a i - t),
  have hp : (1 : ℝ≥0∞) ≤ 2 * m := by norm_cast; linarith,
  have h₁ : ‖f₁ - k • (mu A ∗ f)‖_[2 * m] ≤ k * ε * ‖f‖_[2 * m],
  { rw [L, finset.mem_filter] at ha, exact ha.2 },
  have h₂ : ‖f₂ - k • (mu A ∗ f)‖_[2 * m] ≤ k * ε * ‖f‖_[2 * m],
  { rw [L, finset.mem_filter, L_prop] at ha',
    refine ha'.2.trans_eq' _,
    congr' with i : 1,
    simp [f₂, sub_sub] },
  have h₃ : f₂ = τ t f₁,
  { ext i : 1,
    rw translate_apply,
    refine finset.sum_congr rfl (λ j hj, _),
    rw sub_right_comm },
  have h₄₁ : ‖τ t f₁ - k • (mu A ∗ f)‖_[2 * m] = ‖τ (-t) (τ t f₁ - k • (mu A ∗ f))‖_[2 * m],
  { rw Lpnorm_translate },
  have h₄ : ‖τ t f₁ - k • (mu A ∗ f)‖_[2 * m] = ‖f₁ - τ (-t) (k • (mu A ∗ f))‖_[2 * m],
  { rw [h₄₁, translate_sub_right, translate_translate],
    simp },
  have h₅₁ : ‖τ (-t) (k • (mu A ∗ f)) - f₁‖_[2 * m] ≤ k * ε * ‖f‖_[2 * m],
  { rwa [Lpnorm_sub_comm, ←h₄, ←h₃] },
  have : (0 : ℝ) < k, by positivity,
  refine le_of_mul_le_mul_left _ this,
  rw [←nsmul_eq_mul, ←Lpnorm_nsmul' hp _ (_ - mu A ∗ f), nsmul_sub,
    ←translate_smul_right (-t) (mu A ∗ f) k, mul_assoc, mul_left_comm, two_mul ((k : ℝ) * _),
    ←mul_assoc],
  exact (Lpnorm_sub_le_Lpnorm_sub_add_Lpnorm_sub hp).trans (add_le_add h₅₁ h₁),
end

lemma big_shifts_step2 (L : finset (fin k → G)) (hk : k ≠ 0) :
  (∑ x in L + S.wide_diag k, ∑ l in L, ∑ s in S.wide_diag k, ite (l + s = x) (1 : ℝ) 0) ^ 2 ≤
    (L + S.wide_diag k).card * S.card * ∑ l₁ l₂ in L, ite (l₁ - l₂ ∈ fintype_wide_diag G k) 1 0 :=
begin
  refine sq_sum_le_card_mul_sum_sq.trans _,
  simp_rw [sq, sum_mul, @sum_comm _ _ _ _ (L + S.wide_diag k), boole_mul, sum_ite_eq, mul_assoc],
  refine mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _),
  have : ∀ f : (fin k → G) → (fin k → G) → ℝ,
    ∑ x in L, ∑ y in S.wide_diag k, ite (x + y ∈ L + S.wide_diag k) (f x y) 0 =
    ∑ x in L, ∑ y in S.wide_diag k, f x y,
  { intro f,
    refine sum_congr rfl (λ x hx, _),
    exact sum_congr rfl (λ y hy, if_pos $ add_mem_add hx hy), },
  rw this,
  have : ∀ x y, ∑ s₁ s₂ in S.wide_diag k, ite (y + s₂ = x + s₁) (1 : ℝ) 0 = ite (x - y ∈
    fintype_wide_diag G k) 1 0 * ∑ s₁ s₂ in S.wide_diag k, ite (s₂ = x + s₁ - y) 1 0,
  { intros x y,
    simp_rw [mul_sum],
    refine sum_congr rfl (λ s₁ hs₁, _),
    refine sum_congr rfl (λ s₂ hs₂, _),
    rw [←ite_and_mul_zero, mul_one],
    refine if_congr _ rfl rfl,
    rw [eq_sub_iff_add_eq', and_iff_right_of_imp],
    intro h,
    simp only [mem_wide_diag] at hs₁ hs₂,
    have : x - y = s₂ - s₁,
    { rw [sub_eq_sub_iff_add_eq_add, ←h, add_comm] },
    rw this,
    obtain ⟨i, hi, rfl⟩ := hs₁,
    obtain ⟨j, hj, rfl⟩ := hs₂,
    exact mem_image.2 ⟨j - i, mem_univ _, rfl⟩ },
  simp_rw [@sum_comm _ _ _ _ (S.wide_diag k) L, this, sum_ite_eq'],
  have : ∑ x y in L, ite (x - y ∈ fintype_wide_diag G k) (1 : ℝ) 0 * ∑ z in S.wide_diag k, ite (x +
    z - y ∈ S.wide_diag k) 1 0 ≤ ∑ x y in L, ite (x - y ∈ fintype_wide_diag G k) 1 0 * S.card,
  { refine sum_le_sum (λ l₁ hl₁, sum_le_sum $ λ l₂ hl₂, _),
    refine mul_le_mul_of_nonneg_left _ (by split_ifs; norm_num),
    refine (sum_le_card_nsmul _ _ 1 _).trans_eq _,
    { intros x hx, split_ifs; norm_num },
    rw [card_wide_diag hk],
    simp only [nsmul_one] },
  refine this.trans _,
  simp_rw [←sum_mul, mul_comm],
end

-- might be true for dumb reason when k = 0, since L would be singleton and rhs is |G|,
-- so its just |S| ≤ |G|
lemma big_shifts {A : finset G} (S : finset G) (L : finset (fin k → G)) (hk : k ≠ 0)
  (hL' : L.nonempty) (hL : L ⊆ fintype.pi_finset (λ _, A)) :
  ∃ a : fin k → G, a ∈ L ∧
    L.card * S.card ≤ (A + S).card ^ k * (univ.filter (λ t : G, a - (λ _, t) ∈ L)).card :=
begin
  rcases S.eq_empty_or_nonempty with rfl | hS,
  { simpa only [card_empty, mul_zero, zero_le', and_true] using hL' },
  have hS' : 0 < S.card,
  { rwa card_pos },
  have : (L + S.wide_diag k).card ≤ (A + S).card ^ k,
  { refine (card_le_of_subset (add_subset_add_right hL)).trans _,
    rw ←card_pi_finset_fin_const,
    refine card_le_of_subset _,
    intros i hi,
    simp only [mem_add, mem_wide_diag, fintype.mem_pi_finset, exists_prop, exists_and_distrib_left,
      exists_exists_and_eq_and] at hi ⊢,
    obtain ⟨y, hy, a, ha, rfl⟩ := hi,
    intros j,
    exact ⟨y j, hy _, a, ha, rfl⟩ },
  rsuffices ⟨a, ha, h⟩ : ∃ a ∈ L,
    L.card * S.card ≤ (L + S.wide_diag k).card * (univ.filter (λ t : G, a - (λ _, t) ∈ L)).card,
  { exact ⟨a, ha, h.trans (nat.mul_le_mul_right _ this)⟩ },
  clear_dependent A,
  have : L.card ^ 2 * S.card ≤ (L + S.wide_diag k).card *
    ∑ l₁ l₂ in L, ite (l₁ - l₂ ∈ fintype_wide_diag G k) 1 0,
  { refine nat.le_of_mul_le_mul_left _ hS',
    rw [mul_comm, mul_assoc, ←sq, ←mul_pow, mul_left_comm, ←mul_assoc, ←big_shifts_step1 L hk],
    exact_mod_cast @big_shifts_step2 G _ _ _ _ _ L hk },
  simp only [reindex_count L hk hL'] at this,
  rw [sq, mul_assoc, ←smul_eq_mul, mul_sum] at this,
  rw ←sum_const at this,
  exact exists_le_of_sum_le hL' this,
end

lemma T_bound {K : ℝ} (hK' : 2 ≤ K) (Lc Sc Ac ASc Tc : ℕ) (hk : k = ⌈(64 : ℝ) * m / (ε / 2) ^ 2⌉₊)
  (h₁ : Lc * Sc ≤ ASc ^ k * Tc) (h₂ : (Ac : ℝ) ^ k / 2 ≤ Lc) (h₃ : (ASc : ℝ) ≤ K * Ac)
  (hAc : 0 < Ac) (hε : 0 < ε) (hε' : ε ≤ 1) (hm : 1 ≤ m) :
  K ^ (-512 * m / ε ^ 2 : ℝ) * Sc ≤ Tc :=
begin
  have hk' : k = ⌈(256 : ℝ) * m / ε ^ 2⌉₊,
  { rw [hk, div_pow, div_div_eq_mul_div, mul_right_comm],
    congr' 3,
    norm_num },
  have hK : 0 < K,
  { refine zero_lt_two.trans_le hK' },
  have : (0 : ℝ) < Ac ^ k,
  { refine pow_pos _ _,
    rwa nat.cast_pos },
  refine le_of_mul_le_mul_left _ this,
  have : (Ac : ℝ) ^ k ≤ K * Lc,
  { rw div_le_iff' at h₂,
    refine h₂.trans (mul_le_mul_of_nonneg_right hK' (nat.cast_nonneg _)),
    exact zero_lt_two },
  rw [neg_mul, neg_div, real.rpow_neg hK.le, mul_left_comm,
    inv_mul_le_iff (real.rpow_pos_of_pos hK _)],
  refine (mul_le_mul_of_nonneg_right this (nat.cast_nonneg _)).trans _,
  rw mul_assoc,
  rw [←@nat.cast_le ℝ, nat.cast_mul] at h₁,
  refine (mul_le_mul_of_nonneg_left h₁ hK.le).trans _,
  rw [nat.cast_mul, ←mul_assoc, ←mul_assoc, nat.cast_pow],
  refine mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _),
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (nat.cast_nonneg _) h₃ k) hK.le).trans _,
  rw [mul_pow, ←mul_assoc, ←pow_succ],
  refine mul_le_mul_of_nonneg_right _ (pow_nonneg (nat.cast_nonneg _) _),
  rw [←real.rpow_nat_cast],
  refine real.rpow_le_rpow_of_exponent_le (one_le_two.trans hK') _,
  rw [nat.cast_add_one, ←le_sub_iff_add_le, hk'],
  refine (nat.ceil_lt_add_one _).le.trans _,
  { positivity },
  have : (1 : ℝ) ≤ 128 * (m / ε ^ 2),
  { rw [div_eq_mul_one_div],
    refine one_le_mul_of_one_le_of_one_le (by norm_num1) _,
    refine one_le_mul_of_one_le_of_one_le (nat.one_le_cast.2 hm) _,
    refine one_le_one_div (by positivity) _,
    rw sq_le_one_iff hε.le,
    exact hε' },
  rw [mul_div_assoc, mul_div_assoc],
  linarith only [this]
end

-- trivially true for other reasons for big ε
theorem almost_periodicity {A S : finset G} {K : ℝ} (hm : 1 ≤ m) (hK' : 2 ≤ K)
  (hε : 0 < ε) (hε' : ε ≤ 1) (hK : ((A + S).card : ℝ) ≤ K * A.card) :
  ∃ T : finset G, K ^ (-512 * m / ε ^ 2 : ℝ) * S.card ≤ T.card ∧
    ∀ t ∈ T, ‖τ t (mu A ∗ f) - mu A ∗ f‖_[2 * m] ≤ ε * ‖f‖_[2 * m] :=
begin
  rcases A.eq_empty_or_nonempty with rfl | hA,
  { refine ⟨univ, _, _⟩,
    { have : K ^ ((-512 : ℝ) * m / ε ^ 2) ≤ 1,
      { refine real.rpow_le_one_of_one_le_of_nonpos (one_le_two.trans hK') _,
        rw [neg_mul, neg_div, right.neg_nonpos_iff],
        exact div_nonneg (mul_nonneg (by norm_num1) (nat.cast_nonneg _)) (sq_nonneg _), },
      refine (mul_le_mul_of_nonneg_right this (nat.cast_nonneg _)).trans _,
      rw [one_mul, nat.cast_le],
      exact card_le_of_subset (subset_univ _) },
    intros t ht,
    simp only [mu_empty, zero_conv, translate_zero_right, sub_self, Lpnorm_zero],
    exact mul_nonneg hε.le Lpnorm_nonneg },
  let k := ⌈(64 : ℝ) * m / (ε / 2) ^ 2⌉₊,
  have hk : k ≠ 0,
  { rw [←pos_iff_ne_zero, nat.ceil_pos],
    positivity },
  let L := L k m (ε / 2) f A,
  have : (A.card : ℝ) ^ k / 2 ≤ L.card := lemma28 (half_pos hε) hm (nat.le_ceil _),
  have hL : L.nonempty,
  { rw [←card_pos, ←@nat.cast_pos ℝ],
    refine this.trans_lt' _,
    refine div_pos (pow_pos _ _) zero_lt_two,
    rw [nat.cast_pos, card_pos],
    exact hA },
  obtain ⟨a, ha, hL'⟩ := big_shifts S _ hk hL (filter_subset _ _),
  refine ⟨univ.filter (λ t : G, a + (λ _, -t) ∈ L), _, _⟩,
  { refine T_bound hK' L.card S.card A.card (A + S).card _ rfl _ this hK _ hε hε' hm,
    swap,
    { rwa card_pos },
    convert hL' using 5,
    ext i,
    congr' 2,
    ext j,
    simp [sub_eq_add_neg] },
  intros t ht,
  simp only [exists_prop, exists_eq_right, mem_filter, mem_univ, true_and] at ht,
  have := just_the_triangle_inequality ha ht hk.bot_lt hm,
  rwa [neg_neg, mul_div_cancel' _ (two_ne_zero' ℝ)] at this,
end

end almost_periodicity
