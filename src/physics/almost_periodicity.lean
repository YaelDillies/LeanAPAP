import prereqs.misc
import prereqs.convolution
import algebra.order.chebyshev
import combinatorics.pigeonhole

/-!
# Almost-periodicity
-/

variables {G : Type*} [decidable_eq G] [add_comm_group G]

open finset
open_locale big_operators pointwise ennreal

namespace almost_periodicity

def L_prop [fintype G] (k m : ℕ) (ε : ℝ) (f : G → ℂ) (A : finset G) (a : fin k → G) : Prop :=
‖λ x : G, ∑ i : fin k, f (x - a i) - (k • (mu A ∗ f)) x‖_[2 * m] ≤ k * ε * ‖f‖_[2 * m]

noncomputable instance [fintype G] (k m : ℕ) (ε : ℝ) (f : G → ℂ) (A : finset G) :
  decidable_pred (L_prop k m ε f A) := classical.dec_pred _

noncomputable def L [fintype G] (k m : ℕ) (ε : ℝ) (f : G → ℂ) (A : finset G) : finset (fin k → G) :=
((fintype.pi_finset (λ i : fin k, A)).filter (L_prop k m ε f A))

lemma lemma28 [fintype G] {ε : ℝ} {m : ℕ} {A : finset G} {f : G → ℂ} {k : ℕ}
  (hε : 0 < ε) (hm : 1 ≤ m) (hk : (256 : ℝ) * m / ε ^ 2 ≤ k) :
  A.card ^ k / 2 ≤ (L k m ε f A).card :=
sorry

lemma just_the_triangle_inequality [fintype G] {ε : ℝ} {m : ℕ} {A : finset G} {f : G → ℂ} {k : ℕ}
  {t : G} {a : fin k → G} (ha : a ∈ L k m ε f A) (ha' : a + (λ _, t) ∈ L k m ε f A) (hk : 0 < k)
  (hm : 1 ≤ m) :
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
  { rwa [Lpnorm_sub_comm hp, ←h₄, ←h₃] },
  have : (0 : ℝ) < k, by positivity,
  refine le_of_mul_le_mul_left _ this,
  rw [←nsmul_eq_mul, ←Lpnorm_nsmul' hp _ (_ - mu A ∗ f), nsmul_sub, ←translate_smul_right,
    mul_assoc, mul_left_comm, two_mul ((k : ℝ) * _), ←mul_assoc],
  exact (Lpnorm_sub_le_Lpnorm_sub_add_Lpnorm_sub hp).trans (add_le_add h₅₁ h₁),
end

lemma big_shifts_step1 {k : ℕ} {S : finset G} (L : finset (fin k → G)) (hk : k ≠ 0) :
  ∑ x in L + S.wide_diag k, ∑ l in L, ∑ s in S.wide_diag k, ite (l + s = x) 1 0 =
    L.card * S.card :=
begin
  simp only [@sum_comm _ _ _ _ (L + _), sum_ite_eq],
  rw sum_const_nat,
  intros l hl,
  rw [sum_const_nat, mul_one, finset.card_wide_diag hk],
  intros s hs,
  rw if_pos,
  exact add_mem_add hl hs,
end

variables [fintype G]
lemma big_shifts_step2 {k : ℕ} {S : finset G} (L : finset (fin k → G)) (hk : k ≠ 0) :
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
    refine sum_congr rfl (λ y hy, _),
    rw if_pos,
    exact add_mem_add hx hy },
  rw this,
  have : ∀ x y, ∑ s₁ s₂ in S.wide_diag k, ite (y + s₂ = x + s₁) (1 : ℝ) 0 = ite (x - y ∈
    fintype_wide_diag G k) 1 0 * ∑ s₁ s₂ in S.wide_diag k, ite (s₂ = x + s₁ - y) 1 0,
  { intros x y,
    simp_rw [mul_sum],
    refine sum_congr rfl (λ s₁ hs₁, _),
    refine sum_congr rfl (λ s₂ hs₂, _),
    rw [←ite_and_mul_zero, mul_one],
    refine if_congr _ rfl rfl,
    rw eq_sub_iff_add_eq',
    rw and_iff_right_of_imp,
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
  { refine sum_le_sum (λ l₁ hl₁, _),
    refine sum_le_sum (λ l₂ hl₂, _),
    refine mul_le_mul_of_nonneg_left _ (by split_ifs; norm_num),
    refine (sum_le_card_nsmul _ _ 1 _).trans_eq _,
    { intros x hx, split_ifs; norm_num },
    rw [card_wide_diag hk],
    simp only [nsmul_one] },
  refine this.trans _,
  simp_rw [←sum_mul, mul_comm],
end

lemma card_pi_finset_const {α K : Type*} [fintype K] [decidable_eq K] (A : finset α) :
  (fintype.pi_finset (λ _ : K, A)).card = A.card ^ fintype.card K :=
by rw [fintype.card_pi_finset, prod_const, card_univ]

lemma card_pi_finset_fin_const {α : Type*} {k : ℕ} (A : finset α) :
  (fintype.pi_finset (λ _ : fin k, A)).card = A.card ^ k :=
by rw [card_pi_finset_const, fintype.card_fin]

lemma pi_finset_add {α : Type*} {δ : α → Type*} [Π a : α, decidable_eq (δ a)]
  [Π a : α, has_add (δ a)] [fintype α] [decidable_eq α]
  {s t : Π a : α, finset (δ a)} :
  fintype.pi_finset s + fintype.pi_finset t = fintype.pi_finset (s + t) :=
begin
  ext i,
  simp only [fintype.mem_pi_finset, pi.add_apply, mem_add],
  split,
  { rintro ⟨y, z, hy, hz, rfl⟩ a,
    exact ⟨_, _, hy _, hz _, rfl⟩ },
  intro h,
  choose y z hy hz hi using h,
  exact ⟨y, z, hy, hz, funext hi⟩,
end

lemma sum_ite_zero' {α : Type*} (s : finset α) (p : α → Prop) [decidable_pred p]
  (h : ∀ i j ∈ s, p i → p j → i = j) :
  ∑ i in s, ite (p i) 1 0 = ite (∃ i ∈ s, p i) 1 0 :=
sum_ite_zero (λ i hi j hj, by simpa only [function.on_fun_apply, Prop.disjoint_iff, not_imp_not,
  and_imp] using h i hi j hj) _

lemma ite_fintype_exists (α : Type*) [fintype α] (p : α → Prop) [decidable_pred p]
  (h : ∀ i j, p i → p j → i = j) :
  ∑ i, ite (p i) 1 0 = ite (∃ i, p i) 1 0 :=
by { rw sum_ite_zero' univ p (by simpa using h), simp }

lemma reindex_count {k : ℕ} {S : finset G} (L : finset (fin k → G)) (hk : k ≠ 0) (hL' : L.nonempty)
  (hS : S.nonempty) (l₁ : fin k → G) :
    ∑ l₂ in L, ite (l₁ - l₂ ∈ fintype_wide_diag G k) 1 0 =
      (univ.filter (λ t, (l₁ - λ _, t) ∈ L)).card :=
calc
  ∑ (l₂ : fin k → G) in L, ite (l₁ - l₂ ∈ fintype_wide_diag G k) 1 0 =
    ∑ l₂ in L, ∑ t : G, ite (l₁ - (λ _, t) = l₂) 1 0 :
      begin
        refine sum_congr rfl (λ l₂ hl₂, _),
        rw ite_fintype_exists,
        simp only [mem_fintype_wide_diag, @eq_comm _ l₁, eq_sub_iff_add_eq, sub_eq_iff_eq_add'],
        rintro i j h rfl,
        cases k,
        { simpa using hk },
        { simpa using congr_fun h 0 }
      end
  ... = (univ.filter (λ t, (l₁ - λ _, t) ∈ L)).card :
    begin
      rw sum_comm,
      simp only [sum_ite_eq],
      rw [card_eq_sum_ones, sum_filter],
    end

lemma pigeonhole_test {α β : Type*} [linear_ordered_cancel_add_comm_monoid β] {a : β} {s : finset α}
  (f : α → β) (hs : s.nonempty) (h : s.card • a ≤ ∑ i in s, f i) :
  ∃ i ∈ s, a ≤ f i :=
begin
  by_contra',
  have := (sum_lt_sum_of_nonempty hs this).trans_le' h,
  simpa using this,
end

-- might be true for dumb reason when k = 0, since L would be singleton and rhs is |G|,
-- so its just |S| ≤ |G|
lemma big_shifts {k : ℕ} {A S : finset G} (L : finset (fin k → G)) (hk : k ≠ 0)
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
    exact_mod_cast @big_shifts_step2 G _ _ _ k S L hk },
  simp only [reindex_count L hk hL' hS] at this,
  rw [sq, mul_assoc, ←smul_eq_mul, mul_sum] at this,
  exact pigeonhole_test _ hL' this,
end

-- trivially true for other reasons for big ε
theorem almost_periodicity {ε : ℝ} {A S : finset G} {K : ℝ} {f : G → ℂ} {m : ℕ}
  (hε : 0 < ε) (hε' : ε ≤ 1) (hK : ((A + S).card : ℝ) ≤ K * A.card) :
  ∃ T : finset G, K ^ (-2048 * m / ε ^ 2 : ℝ) * S.card ≤ T.card ∧
    ∀ t ∈ T, ‖τ t (mu A ∗ f) - mu A ∗ f‖_[2 * m] ≤ ε * ‖f‖_[2 * m] :=
sorry

end almost_periodicity
