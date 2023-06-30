import algebra.big_operators.order
import analysis.mean_inequalities_pow
import data.fin.tuple.nat_antidiagonal
import data.fintype.big_operators
import mathlib.algebra.big_operators.basic
import prereqs.multinomial

open finset fintype nat
open_locale big_operators

variables {G : Type*} {n m : ℕ}

@[reducible] def pi_finset_const (A : finset G) (n : ℕ) := fintype.pi_finset (λ _ : fin n, A)

local infix `^^`:70 := pi_finset_const

lemma step_one {A : finset G} (hA : A.nonempty) (f : G → ℝ) (a : fin n → G)
  (hf : ∀ i : fin n, ∑ a in A^^n, f (a i) = 0) :
  |∑ i, f (a i)| ^ (m + 1) ≤
    (∑ b in A^^n, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / A.card ^ n :=
calc
  |∑ i, f (a i)| ^ (m + 1) =
    |∑ i, (f (a i) - (∑ b in A^^n, f (b i)) / (A^^n).card)| ^ (m + 1) :
      by simp only [hf, sub_zero, zero_div]
  ... = |(∑ b in A^^n, ∑ i, (f (a i) - f (b i))) / (A^^n).card| ^ (m + 1) :
    begin
      simp only [sum_sub_distrib],
      rw [sum_const, sub_div, sum_comm, sum_div, nsmul_eq_mul, card_pi_finset, prod_const,
        finset.card_fin, nat.cast_pow, mul_div_cancel_left],
      exact pow_ne_zero _ (nat.cast_ne_zero.2 (finset.card_pos.2 hA).ne'),
    end
  ... = |∑ b in A^^n, ∑ i, (f (a i) - f (b i))| ^ (m + 1) / (A^^n).card ^ (m + 1) :
    by rw [abs_div, div_pow, nat.abs_cast]
  ... ≤ (∑ b in A^^n, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / (A^^n).card ^ (m + 1) :
    div_le_div_of_le (by positivity) (pow_le_pow_of_le_left (by positivity)
      (abv_sum_le_sum_abv _ _) _)
  ... = (∑ b in A^^n, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / (A^^n).card ^ m / (A^^n).card :
    by rw [div_div, ←pow_succ']
  ... ≤ _ :
  begin
    rw sum_div,
    refine (div_le_div_of_le (by positivity) (real.pow_sum_div_card_le_sum_pow (A^^n) m _)).trans _,
    { intros i hi,
      positivity },
    rw [card_pi_finset, prod_const, finset.card_fin, nat.cast_pow, sum_div],
  end

lemma step_one' {A : finset G} (hA : A.nonempty) (f : G → ℝ)
  (hf : ∀ i : fin n, ∑ a in A^^n, f (a i) = 0) (a : fin n → G) :
  |∑ i, f (a i)| ^ m ≤
    (∑ b in A^^n, |∑ i, (f (a i) - f (b i))| ^ m) / A.card ^ n :=
begin
  cases m,
  { simp only [pow_zero, sum_const, prod_const, nat.smul_one_eq_coe, finset.card_fin,
      card_pi_finset, ←nat.cast_pow],
    rw div_self,
    rw [nat.cast_ne_zero, ←pos_iff_ne_zero],
    exact pow_pos (finset.card_pos.2 hA) _ },
  exact step_one hA f a hf
end

-- works with this
-- lemma step_two_aux' {β γ : Type*} [add_comm_monoid β] [comm_ring γ] {A : finset G}
--   (f : (fin n → G) → (fin n → γ)) (ε : fin n → γ)
--   (hε : ∀ i : fin n, ε i = -1 ∨ ε i = 1) (g : (fin n → γ) → β) :
--   ∑ a b in A^^n, g (ε * (f a - f b)) = ∑ a b in A^^n, g (f a - f b) :=
-- feels like could generalise more...
-- the key point is that you combine the double sums into a single sum, and do a pair swap
-- when the corresponding ε is -1
-- but the order here is a bit subtle (ie this explanation is an oversimplification)

lemma step_two_aux (A : finset G) (f : G → ℝ) (ε : fin n → ℝ)
  (hε : ε ∈ ({-1, 1} : finset ℝ)^^n) (g : (fin n → ℝ) → ℝ) :
  ∑ a b in A^^n, g (ε * (f ∘ a - f ∘ b)) = ∑ a b in A^^n, g (f ∘ a - f ∘ b) :=
begin
  rw [←sum_product', ←sum_product'],
  let swapper : (fin n → G) × (fin n → G) → (fin n → G) × (fin n → G),
  { intros xy,
    exact (λ i, if ε i = 1 then xy.1 i else xy.2 i, λ i, if ε i = 1 then xy.2 i else xy.1 i) },
  have h₁ : ∀ a ∈ (A^^n) ×ˢ (A^^n), swapper a ∈ (A^^n) ×ˢ (A^^n),
  { intros a,
    simp only [mem_product, and_imp, mem_pi_finset, ←forall_and_distrib],
    intros h i,
    split_ifs,
    { exact h i },
    exact (h i).symm },
  have h₂ : ∀ a ∈ (A^^n) ×ˢ (A^^n), swapper (swapper a) = a,
  { intros a ha,
    ext,
    { simp only, split_ifs; refl },
    { simp only, split_ifs; refl } },
  refine sum_nbij' swapper h₁ _ swapper h₁ h₂ h₂,
  { rintro ⟨a, b⟩ _,
    congr' with i : 1,
    simp only [pi.mul_apply, pi.sub_apply, function.comp_apply],
    simp only [mem_pi_finset, mem_insert, mem_singleton] at hε,
    split_ifs,
    { simp [h] },
    rw (hε i).resolve_right h,
    ring },
end

lemma step_two {A : finset G} (hA : A.nonempty) (f : G → ℝ) :
  ∑ a b in A^^n, (∑ i, (f (a i) - f (b i))) ^ (2 * m) =
    1 / 2 ^ n * ∑ ε in ({-1, 1} : finset ℝ)^^n,
      ∑ a b in A^^n, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) :=
begin
  have : ∀ (ε : fin n → ℝ), ε ∈ ({-1, 1} : finset ℝ)^^n →
    ∑ a b in A^^n, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
      ∑ a b in A^^n, (∑ i, (f (a i) - f (b i))) ^ (2 * m),
  { intros ε hε,
    exact step_two_aux A f _ hε (λ z : fin n → ℝ, (univ.sum z) ^ (2 * m)) },
  rw [sum_congr rfl this, sum_const, card_pi_finset, prod_const, finset.card_fin,
    card_insert_of_not_mem, card_singleton, ←bit0, nsmul_eq_mul, nat.cast_pow, nat.cast_two,
    one_div, inv_mul_cancel_left₀],
  { positivity },
  norm_num
end

lemma step_three {A : finset G} (f : G → ℝ) :
  ∑ ε in ({-1, 1} : finset ℝ)^^n, ∑ a b in A^^n, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m)
    = ∑ a b in A^^n, ∑ k in cut (univ : finset (fin n)) (2 * m),
      multinomial univ k * (∏ t, (f (a t) - f (b t)) ^ k t) *
        ∑ ε in ({-1, 1} : finset ℝ)^^n, ∏ t, ε t ^ k t :=
begin
  simp only [@sum_comm _ _ (fin n → ℝ) _ _ (A^^n), ←complex.abs_pow, multinomial_expansion'],
  refine sum_congr rfl (λ a ha, _),
  refine sum_congr rfl (λ b hb, _),
  simp only [mul_pow, prod_mul_distrib, @sum_comm _ _ (fin n → ℝ), ←mul_sum, ←sum_mul],
  refine sum_congr rfl (λ k hk, _),
  rw [←mul_assoc, mul_right_comm],
end

lemma step_four {k : fin n → ℕ} :
  ∑ ε in ({-1, 1} : finset ℝ)^^n, ∏ t, ε t ^ k t = 2 ^ n * ite (∀ i, even (k i)) 1 0 :=
begin
  have := sum_prod_pi_finset ({-1, 1} : finset ℝ) (λ i fi, fi ^ k i),
  dsimp at this,
  rw [pi_finset_const, this, ←fintype.prod_boole],
  have : (2 : ℝ) ^ n = ∏ i : fin n, 2,
  { simp },
  rw [this, ←prod_mul_distrib],
  refine prod_congr rfl (λ t ht, _),
  rw [sum_pair, one_pow, mul_boole],
  swap,
  { norm_num },
  split_ifs,
  { rw [h.neg_one_pow, bit0] },
  rw ←nat.odd_iff_not_even at h,
  rw [h.neg_one_pow],
  simp
end

lemma sum_div_nat {α : Type*} {s : finset α} {f : α → ℕ} {b : ℕ} (hf : ∀ i ∈ s, b ∣ f i) :
  ∑ i in s, (f i / b) = (∑ i in s, f i) / b :=
begin
  rcases b.eq_zero_or_pos with rfl | hb,
  { simp },
  rw [eq_comm, nat.div_eq_iff_eq_mul_left hb (finset.dvd_sum hf), sum_mul],
  refine sum_congr rfl (λ s hs, _),
  rw nat.div_mul_cancel (hf _ hs),
end

lemma step_five {α : Type*} {s : finset α} :
  (cut s (2 * m)).filter (λ a : α → ℕ, ∀ i ∈ s, even (a i)) =
    (cut s m).map
      ⟨λ f a, 2 * f a, λ f g h, funext $ λ i, mul_right_injective₀ two_ne_zero (congr_fun h i)⟩ :=
begin
  ext f,
  simp only [mem_map, mem_filter, mem_cut, function.embedding.coe_fn_mk, exists_prop, and_assoc],
  split,
  { rintro ⟨fsum, fsup, feven⟩,
    simp only [even_iff_two_dvd] at feven,
    refine ⟨λ i, f i / 2, _⟩,
    rw [sum_div_nat feven, fsum, nat.mul_div_cancel_left _ zero_lt_two],
    simp only [eq_self_iff_true, true_and, function.funext_iff],
    refine ⟨λ i hi, _, λ i, _⟩,
    { rw [fsup _ hi, nat.zero_div] },
    by_cases i ∈ s,
    { rw nat.mul_div_cancel' (feven _ h) },
    rw [fsup _ h, nat.zero_div, mul_zero] },
  rintro ⟨f, rfl, hf, rfl⟩,
  rw [←mul_sum],
  simpa using hf
end

lemma step_five' {α : Type*} [fintype α] :
  (cut univ (2 * m)).filter (λ a : α → ℕ, ∀ i : α, even (a i)) =
    (cut univ m).map
      ⟨λ f a, 2 * f a, λ f g h, funext $ λ i, mul_right_injective₀ two_ne_zero (congr_fun h i)⟩ :=
by simp [←step_five]

-- double_multinomial
lemma step_six {f : G → ℝ} {a b : fin n → G} :
  ∑ (k : fin n → ℕ) in cut univ m,
    (multinomial univ (λ a, 2 * k a) : ℝ) * ∏ i : fin n, (f (a i) - f (b i)) ^ (2 * k i) ≤
  m ^ m * (∑ i : fin n, (f (a i) - f (b i)) ^ 2) ^ m :=
begin
  rw [multinomial_expansion', mul_sum],
  refine sum_le_sum (λ k hk, _),
  rw mem_cut at hk,
  simp only [←mul_assoc, pow_mul],
  refine mul_le_mul_of_nonneg_right _ _,
  swap,
  { refine prod_nonneg _,
    intros i hi,
    exact pow_nonneg (sq_nonneg _) _ },
  norm_cast,
  refine double_multinomial.trans _,
  rw hk.1,
end


lemma small_ineq {a b : ℝ} : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) :=
begin
  have := real.pow_arith_mean_le_arith_mean_pow_of_even univ ![1/2, 1/2] ![a, b]
    (by simp [fin.forall_fin_two]) (by norm_num) even_two,
  simp only [fin.sum_univ_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons,
    sq] at this,
  linarith
end

lemma other_small_ineq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) :
  (a + b) ^ m ≤ 2 ^ (m - 1) * (a ^ m + b ^ m) :=
begin
  cases m,
  { simp },
  rw [nat.succ_sub_one, ←div_le_iff'],
  swap, { positivity },
  have := @real.pow_sum_div_card_le_sum_pow _ univ ![a, b] m (by simp [fin.forall_fin_two, *]),
  simpa using this
end

lemma step_seven {f : G → ℝ} {a b : fin n → G} :
  ↑m ^ m * (∑ i : fin n, (f (a i) - f (b i)) ^ 2) ^ m ≤
    m ^ m * 2 ^ m * (∑ i : fin n, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m :=
begin
  rw [←mul_pow, ←mul_pow, ←mul_pow],
  refine pow_le_pow_of_le_left _ _ _,
  { exact mul_nonneg (nat.cast_nonneg _) (sum_nonneg (λ i hi, by positivity)) },
  rw [mul_assoc],
  refine mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _),
  rw mul_sum,
  refine sum_le_sum (λ i hi, _),
  rw sub_eq_add_neg,
  refine small_ineq.trans_eq _,
  simp,
end

lemma step_eight {f : G → ℝ} {a b : fin n → G} :
  (m : ℝ) ^ m * 2 ^ m * (∑ i : fin n, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m ≤
    (m : ℝ) ^ m * 2 ^ (m + (m - 1)) *
      ((∑ i : fin n, f (a i) ^ 2) ^ m + (∑ i : fin n, f (b i) ^ 2) ^ m) :=
begin
  rw [pow_add, ←mul_assoc _ _ ((2 : ℝ) ^ _), mul_assoc _ ((2 : ℝ) ^ (m - 1))],
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  rw sum_add_distrib,
  refine (other_small_ineq _ _ m),
  { refine sum_nonneg (λ i hi, _),
    positivity },
  { refine sum_nonneg (λ i hi, _),
    positivity },
end

lemma end_step {A : finset G} {f : G → ℝ} (hm : 1 ≤ m) (hA : A.nonempty) :
  (∑ a b in A^^n, ∑ (k : fin n → ℕ) in cut univ m,
    ↑(multinomial univ (λ i, 2 * k i)) * ∏ (t : fin n), (f (a t) - f (b t)) ^ (2 * k t))
      / A.card ^ n ≤
  ((4 * m) ^ m * ∑ a in A^^n, (∑ i, f (a i) ^ 2) ^ m) :=
calc
  (∑ a b in A^^n, ∑ (k : fin n → ℕ) in cut univ m,
    (multinomial univ (λ i, 2 * k i) : ℝ) * ∏ t, (f (a t) - f (b t)) ^ (2 * k t))
      / A.card ^ n ≤
    (∑ a b in A^^n, (m : ℝ) ^ m * 2 ^ m * (∑ i : fin n, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m)
      / A.card ^ n : div_le_div_of_le (pow_nonneg (nat.cast_nonneg _) _)
      begin
        refine sum_le_sum (λ a ha, _),
        refine sum_le_sum (λ b hb, _),
        exact step_six.trans step_seven,
      end
  ... ≤ (∑ a b in A^^n, (m : ℝ) ^ m * 2 ^ (m + (m - 1)) *
      ((∑ i : fin n, f (a i) ^ 2) ^ m + (∑ i : fin n, f (b i) ^ 2) ^ m))
      / A.card ^ n : div_le_div_of_le (pow_nonneg (nat.cast_nonneg _) _)
      begin
        refine sum_le_sum (λ a ha, _),
        refine sum_le_sum (λ b hb, _),
        refine step_eight
      end
  ... = _ :
    begin
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul, ←mul_sum],
      rw [←mul_add, ←two_mul, ←mul_assoc, mul_assoc _ (2 ^ _ : ℝ), ←pow_succ', add_assoc,
        nat.sub_add_cancel hm, card_pi_finset, prod_const, finset.card_fin, mul_div_assoc,
        ←nat.cast_pow A.card, mul_div_cancel_left],
      swap,
      { rw [nat.cast_ne_zero, ←pos_iff_ne_zero],
        exact pow_pos (finset.card_pos.2 hA) _ },
      rw [←two_mul, pow_mul, ←mul_pow, mul_comm (m : ℝ), sq, ←bit0_eq_two_mul],
    end

lemma basic_marcinkiewicz_zygmund {A : finset G} (f : G → ℝ)
  (hf : ∀ i : fin n, ∑ a in A^^n, f (a i) = 0) :
  ∑ a in A^^n, |∑ i, f (a i)| ^ (2 * m) ≤ (4 * m) ^ m * ∑ a in A^^n, (∑ i, |f (a i)| ^ 2) ^ m :=
begin
  rcases m.eq_zero_or_pos with rfl | hm,
  { simp },
  have hm' : 1 ≤ m,
  { rwa [nat.succ_le_iff] },
  rcases A.eq_empty_or_nonempty with rfl | hA,
  { cases n,
    { cases m; simp },
    { rw [pi_finset_const, pi_finset_empty, finset.sum_empty],
      cases m; simp } },
  refine (sum_le_sum (λ a (_ : a ∈ A^^n), @step_one' _ _ (2 * m) _ hA f hf a)).trans _,
  rw [←sum_div],
  simp only [pow_mul, sq_abs],
  simp only [←pow_mul],
  rw [step_two hA, step_three, mul_comm, mul_one_div, div_div],
  simp only [step_four, mul_ite, mul_zero, mul_one],
  simp only [←sum_filter, ←sum_mul],
  rw [mul_comm, mul_div_mul_left],
  swap, { positivity },
  simp only [step_five', sum_map, function.embedding.coe_fn_mk],
  exact (end_step hm' hA),
end

-- works for m = 0 but the statement is weird, and there might be a useful statement for that case
lemma other_marcinkiewicz_zygmund {A : finset G} (f : G → ℝ) (hm : m ≠ 0)
  (hf : ∀ i : fin n, ∑ a in A^^n, f (a i) = 0) :
  ∑ a in A^^n, |∑ i, f (a i)| ^ (2 * m) ≤
    (4 * m) ^ m * n ^ (m - 1) * ∑ a in A^^n, ∑ i, |f (a i)| ^ (2 * m) :=
begin
  cases m,
  { simpa using hm },
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp },
  refine (basic_marcinkiewicz_zygmund f hf).trans _,
  rw mul_assoc,
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  rw nat.succ_sub_one,
  simp only [pow_mul, mul_sum],
  refine sum_le_sum (λ a ha, _),
  rw [←mul_sum],
  refine (mul_le_mul_of_nonneg_left (real.pow_sum_div_card_le_sum_pow _ _ _) _).trans' _,
  { intros i hi,
    positivity },
  { positivity },
  rw [finset.card_fin, mul_div_cancel'],
  positivity
end

lemma other_marcinkiewicz_zygmund' {A : finset G} (f : G → ℝ) (hm : m ≠ 0)
  (hf : ∀ i : fin n, ∑ a in A^^n, f (a i) = 0) :
  ∑ a in A^^n, (∑ i, f (a i)) ^ (2 * m) ≤
    (4 * m) ^ m * n ^ (m - 1) * ∑ a in A^^n, ∑ i, f (a i) ^ (2 * m) :=
by simpa only [pow_mul, sq_abs] using other_marcinkiewicz_zygmund f hm hf

lemma right_ineq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {m : ℕ} : a ^ m + b ^ m ≤ 2 * (a + b) ^ m :=
calc a ^ m + b ^ m ≤ 2 * (max a b)^m :
    begin
      rcases max_cases a b with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩),
      { rw [h₁, two_mul, add_le_add_iff_left],
        exact pow_le_pow_of_le_left hb h₂ _ },
      { rw [h₁, two_mul, add_le_add_iff_right],
        exact pow_le_pow_of_le_left ha h₂.le _ },
    end
  ... ≤ 2 * (a + b) ^ m :
    begin
      refine mul_le_mul_of_nonneg_left _ two_pos.le,
      refine pow_le_pow_of_le_left (le_max_of_le_left ha) (max_le_add_of_nonneg ha hb) _,
    end

lemma complex_marcinkiewicz_zygmund {A : finset G} (f : G → ℂ) (hm : m ≠ 0)
  (hf : ∀ i : fin n, ∑ a in A^^n, f (a i) = 0) :
  ∑ a in A^^n, ‖∑ i, f (a i)‖ ^ (2 * m) ≤
    (8 * m) ^ m * n ^ (m - 1) * ∑ a in A^^n, ∑ i, ‖f (a i)‖ ^ (2 * m) :=
begin
  let f₁ : G → ℝ := λ x, (f x).re,
  let f₂ : G → ℝ := λ x, (f x).im,
  have hf₁ : ∀ i, ∑ a in A^^n, f₁ (a i) = 0,
  { intro i, rw [←complex.re_sum, hf, complex.zero_re] },
  have hf₂ : ∀ i, ∑ a in A^^n, f₂ (a i) = 0,
  { intro i, rw [←complex.im_sum, hf, complex.zero_im] },
  have h₁ := other_marcinkiewicz_zygmund' _ hm hf₁,
  have h₂ := other_marcinkiewicz_zygmund' _ hm hf₂,
  simp only [pow_mul, complex.norm_eq_abs, complex.sq_abs, complex.norm_sq_apply],
  simp only [←sq, complex.re_sum, complex.im_sum],
  calc ∑ a in A^^n, ((∑ i, (f (a i)).re) ^ 2 + ((∑ i, (f (a i)).im) ^ 2)) ^ m ≤
    ∑ a in A^^n, 2 ^ (m - 1) * (((∑ i, (f (a i)).re) ^ 2) ^ m + ((∑ i, (f (a i)).im) ^ 2) ^ m) : _
    ... = 2 ^ (m - 1) * ∑ a in A^^n,
      ((∑ i, (f (a i)).re) ^ (2 * m) + (∑ i, (f (a i)).im) ^ (2 * m)) : _
    ... ≤ 2 ^ (m - 1) * (4 * m) ^ m * n ^ (m - 1) * ∑ a in A^^n,
      ∑ i, ((f (a i)).re ^ (2 * m) + (f (a i)).im ^ (2 * m)) : _
    ... ≤ (8 * m) ^ m * n ^ (m - 1) * ∑ a in A^^n,
      ∑ i, ((f (a i)).re ^ 2 + (f (a i)).im ^ 2) ^ m : _,
  { exact sum_le_sum (λ a ha, other_small_ineq (sq_nonneg _) (sq_nonneg _) m) },
  { simp only [mul_sum, pow_mul] },
  { rw [mul_assoc, mul_assoc, sum_add_distrib],
    refine mul_le_mul_of_nonneg_left _ _,
    swap,
    { positivity },
    simp only [sum_add_distrib, mul_add, ←mul_assoc],
    refine add_le_add _ _,
    { exact h₁ },
    { exact h₂ } },
  simp only [mul_sum],
  refine sum_le_sum (λ a ha, _),
  refine sum_le_sum (λ i hi, _),
  rw [pow_mul, pow_mul],
  refine (mul_le_mul_of_nonneg_left (right_ineq (sq_nonneg _) (sq_nonneg _)) _).trans_eq _,
  { positivity },
  rw [mul_assoc (2 ^ _ : ℝ), mul_mul_mul_comm, ←pow_succ', nat.sub_add_cancel, ←mul_assoc,
    ←mul_assoc, ←mul_pow, ←mul_assoc, ←bit0_eq_two_mul],
  rwa [succ_le_iff, pos_iff_ne_zero],
end

lemma image_pi_finset {α : Type*} [decidable_eq α] [fintype α] (δ : α → Type*)
  (t : Π a : α, finset (δ a)) (a : α) [decidable_eq (δ a)]
  (ht : ∀ b, a ≠ b → (t b).nonempty) :
  (pi_finset (λ i : α, t i)).image (λ f, f a) = t a :=
begin
  ext x,
  simp only [mem_image, mem_pi_finset, exists_prop],
  split,
  { rintro ⟨f, hf, rfl⟩,
    exact hf _ },
  intro h,
  choose f hf using ht,
  refine ⟨λ b, if h : a = b then ((@eq.rec α a δ x _ h) : δ b) else f _ h, _, _⟩,
  { intro b,
    split_ifs with h' h',
    { cases h',
      exact h },
    exact hf _ _ },
  simp
end

lemma image_pi_finset_const {α : Type*} [decidable_eq α] [fintype α] (δ : Type*) [decidable_eq δ]
  (t : finset δ) (a : α) : (pi_finset (λ i : α, t)).image (λ f, f a) = t :=
begin
  rcases t.eq_empty_or_nonempty with rfl | ht,
  { haveI : nonempty α := ⟨a⟩,
    simp },
  rw image_pi_finset (λ _, δ),
  simp [ht]
end

lemma filter_pi_finset_card_of_mem {α : Type*} [decidable_eq α] [fintype α] (δ : α → Type*)
  [Π a : α, decidable_eq (δ a)] (t : Π a : α, finset (δ a)) (a : α) (x : δ a) (hx : x ∈ t a) :
  ((pi_finset t).filter (λ f : Π a : α, δ a, f a = x)).card =
    ∏ b in univ.erase a, (t b).card :=
begin
  let t' : Π a : α, finset (δ a) :=
    λ a', if h : a = a' then {(@eq.rec _ _ δ x _ h : δ a')} else t a',
  have : (t' a).card = 1,
  { simp [t'] },
  have h₁ : ∏ b in univ.erase a, (t b).card = ∏ b, (t' b).card,
  { rw ←@prod_erase ℕ α _ _ univ (λ b, (t' b).card) a this,
    refine prod_congr rfl _,
    intros b hb,
    simp only [mem_erase, ne.def, mem_univ, and_true] at hb,
    simp only [t', dif_neg (ne.symm hb)] },
  have h₂ : ∏ b, (t' b).card = ∏ b, ∑ i in t' b, 1,
  { simp },
  rw [h₁, h₂, prod_univ_sum'],
  simp only [prod_const_one, ←finset.card_eq_sum_ones],
  congr' 1,
  ext f,
  simp only [mem_filter, mem_pi_finset, t'],
  split,
  { rintro ⟨hf, rfl⟩ b,
    split_ifs with h₁ h₁,
    { cases h₁,
      simp },
    exact hf _ },
  intro h,
  have : f a = x, { simpa using h a },
  refine ⟨_, this⟩,
  intros b,
  rcases eq_or_ne a b with rfl | hab,
  { rwa this },
  simpa [dif_neg hab] using h b,
end

lemma filter_pi_finset_of_not_mem {α : Type*} [decidable_eq α] [fintype α] (δ : α → Type*)
  [Π a : α, decidable_eq (δ a)] (t : Π a : α, finset (δ a)) (a : α) (x : δ a) (hx : x ∉ t a) :
  (pi_finset t).filter (λ f : Π a : α, δ a, f a = x) = ∅ :=
begin
  simp only [filter_eq_empty_iff, mem_pi_finset],
  rintro f hf rfl,
  exact hx (hf _)
end

lemma filter_pi_finset_const_card_of_mem {α : Type*} [decidable_eq α] [fintype α] (δ : Type*)
  [decidable_eq δ] (t : finset δ) (a : α) (x : δ) (hx : x ∈ t) :
  ((pi_finset (λ _, t)).filter (λ f : α → δ, f a = x)).card = t.card ^ (card α - 1) :=
begin
  rw [filter_pi_finset_card_of_mem (λ _, δ), prod_const t.card, card_erase_of_mem, card_univ],
  { simp },
  { exact hx }
end

-- works better for rewrites
lemma filter_pi_finset_const_of_not_mem {α : Type*} [decidable_eq α] [fintype α] (δ : Type*)
  [decidable_eq δ] (t : finset δ) (a : α) (x : δ) (hx : x ∉ t) :
  (pi_finset (λ _, t)).filter (λ f : α → δ, f a = x) = ∅ :=
filter_pi_finset_of_not_mem (λ _, δ) _ _ _ hx

lemma filter_pi_finset_card {α : Type*} [decidable_eq α] [fintype α] (δ : α → Type*)
  [Π a : α, decidable_eq (δ a)] (t : Π a : α, finset (δ a)) (a : α) (x : δ a) :
  ((pi_finset t).filter (λ f : Π a : α, δ a, f a = x)).card =
    if x ∈ t a then ∏ b in univ.erase a, (t b).card else 0 :=
begin
  split_ifs,
  { rw filter_pi_finset_card_of_mem _ _ _ _ h },
  { rw [filter_pi_finset_of_not_mem _ _ _ _ h, finset.card_empty] }
end

lemma filter_pi_finset_const_card {α : Type*} [decidable_eq α] [fintype α] (δ : Type*)
  [decidable_eq δ] (t : finset δ) (a : α) (x : δ) :
  ((pi_finset (λ _, t)).filter (λ f : α → δ, f a = x)).card =
  if x ∈ t then t.card ^ (card α - 1) else 0 :=
by { rw [filter_pi_finset_card, prod_const t.card, card_erase_of_mem, card_univ], simp }

lemma mean_simpler_condition {A : finset G} (f : G → ℂ) (hf : ∑ a in A, f a = 0) (i : fin n) :
  ∑ a in pi_finset (λ _ : fin n, A), f (a i) = 0 :=
begin
  classical,
  rw sum_comp,
  simp only [image_pi_finset_const, filter_pi_finset_const_card _ A i, ite_smul, zero_smul],
  rw [←sum_filter, filter_mem_eq_inter, inter_self, ←smul_sum, hf, smul_zero],
end
