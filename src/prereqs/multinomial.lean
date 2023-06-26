import data.nat.choose.basic
import algebra.big_operators.order
import data.finset.powerset
import data.fin.tuple.nat_antidiagonal
import mathlib.algebra.big_operators.ring
import data.fin.vec_notation
import data.finset.sort
import prereqs.cut
import prereqs.misc

open_locale big_operators nat
open finset

variables {K : Type*} {s : finset K} {f f' : K → ℕ}

def multinomial (s : finset K) (f : K → ℕ) : ℕ := (∑ i in s, f i)! / ∏ i in s, (f i)!

lemma multinomial_dvd :
  ∏ i in s, (f i)! ∣ (∑ i in s, f i)! :=
begin
  induction s using finset.cons_induction_on with a s has ih,
  { simp },
  rw [prod_cons, sum_cons],
  exact (mul_dvd_mul_left _ ih).trans (nat.factorial_mul_factorial_dvd_factorial_add _ _),
end

@[simp] lemma multinomial_empty : multinomial ∅ f = 1 := by simp [multinomial]

lemma multinomial_congr (h : ∀ x ∈ s, f x = f' x) : multinomial s f = multinomial s f' :=
begin
  rw [multinomial, multinomial, sum_congr rfl h],
  congr' 1,
  refine prod_congr rfl _,
  intros x hx,
  rw h _ hx
end

lemma multinomial_cons {a : K} {s : finset K} (has : a ∉ s) :
  multinomial (s.cons a has) f = nat.choose (f a + ∑ i in s, f i) (f a) * multinomial s f :=
begin
  rw [multinomial, nat.div_eq_iff_eq_mul_left _ multinomial_dvd, prod_cons, multinomial,
    mul_assoc, mul_left_comm _ (f a)!, nat.div_mul_cancel multinomial_dvd, ←mul_assoc,
    nat.choose_symm_add, nat.add_choose_mul_factorial_mul_factorial, sum_cons],
  exact prod_pos (λ i hi, by positivity),
end

lemma multinomial_insert [decidable_eq K] {a : K} {s : finset K} (has : a ∉ s) :
  multinomial (insert a s) f = nat.choose (f a + ∑ i in s, f i) (f a) * multinomial s f :=
by rw [←cons_eq_insert _ _ has, multinomial_cons]

lemma multinomial_expansion {α β : Type*} [comm_semiring β] {x : α → β} {s : finset α} {n : ℕ} :
  (∑ i in s, x i) ^ n = ∑ p in fintype.pi_finset (λ _, s), ∏ i : fin n, x (p i) :=
finset.pow_sum _ _ _

lemma multinomial_expansion' {α β : Type*} [comm_semiring β] {s : finset α} {x : α → β} {n : ℕ} :
  (∑ i in s, x i) ^ n = ∑ k in cut s n, multinomial s k * ∏ t in s, x t ^ k t :=
begin
  classical, -- maybe make cut_cons and use cons_induction
  induction s using finset.induction_on with a s has ih generalizing n,
  { cases n; simp },
  rw [sum_insert has, cut_insert _ _ _ has, sum_bUnion (cut_insert_disjoint_bUnion _ _ _ has)],
  dsimp,
  simp only [sum_map, function.embedding.coe_fn_mk, pi.add_apply, multinomial_insert has,
    pi.add_apply, eq_self_iff_true, if_true, nat.cast_mul, prod_insert has, eq_self_iff_true,
    if_true, sum_add_distrib, sum_ite_eq', has, if_false, add_zero],
  have : ∀ p : ℕ × ℕ, p ∈ n.antidiagonal → ∑ (f : α → ℕ) in cut s p.snd,
    ((f a + p.fst + s.sum f).choose (f a + p.fst) : β) *
      multinomial s (f + λ (t : α), ite (t = a) p.fst 0) *
        (x a ^ (f a + p.fst) * ∏ (t : α) in s, x t ^ (f t + ite (t = a) p.fst 0)) =
    ∑ (f : α → ℕ) in cut s p.snd,
      n.choose p.fst *
        multinomial s f * (x a ^ p.fst * ∏ (t : α) in s, x t ^ f t),
  { intros p hp,
    refine sum_congr rfl (λ f hf, _),
    rw mem_cut at hf,
    rw [hf.2 _ has, zero_add, hf.1],
    congr' 2,
    { rw nat.mem_antidiagonal.1 hp },
    { rw multinomial_congr,
      intros t ht,
      rw [pi.add_apply, if_neg, add_zero],
      exact ne_of_mem_of_not_mem ht has },
    refine prod_congr rfl (λ t ht, _),
    rw [if_neg, add_zero],
      exact ne_of_mem_of_not_mem ht has },
  rw sum_congr rfl this,
  simp only [antidiagonal_eq_map, sum_map, function.embedding.coe_fn_mk],
  rw [add_pow],
  refine sum_congr rfl (λ i hi, _),
  simp only [ih, sum_mul, mul_sum],
  refine sum_congr rfl (λ f hf, _),
  ac_refl
end

-- also shows n!! ≤ (2 * n)!
lemma double_factorial_inequality {m : ℕ} : 2 ^ m * m! ≤ (2 * m)! :=
begin
  induction m with m ih,
  { simp },
  rw [pow_succ, nat.factorial_succ, mul_mul_mul_comm, nat.mul_succ, nat.factorial_succ],
  refine (nat.mul_le_mul_left _ ih).trans (nat.mul_le_mul_left _ _),
  exact nat.factorial_le (nat.le_succ _),
end

lemma other_double_factorial_inequality {m : ℕ} : (2 * m)! ≤ (2 * m) ^ m * m! :=
begin
  rw [two_mul, ←nat.factorial_mul_asc_factorial, mul_comm],
  exact nat.mul_le_mul_right _ (nat.asc_factorial_le_pow_add _ _),
end

lemma double_multinomial :
  multinomial s (λ i, 2 * f i) ≤ (∑ i in s, f i) ^ (∑ i in s, f i) * multinomial s f :=
begin
  rw [multinomial, multinomial, ←mul_sum],
  refine nat.div_le_of_le_mul' _,
  rw ←mul_assoc,
  rw ←nat.mul_div_assoc _ multinomial_dvd,
  rw nat.le_div_iff_mul_le,
  swap,
  { refine prod_pos _,
    intros i hi,
    positivity },
  refine (nat.mul_le_mul_right _ other_double_factorial_inequality).trans _,
  rw [mul_pow, mul_comm, ←mul_assoc, ←mul_assoc],
  refine nat.mul_le_mul_right _ (nat.mul_le_mul_right _ _),
  rw [←finset.pow_sum_but_its_actually_pow_sum, ←prod_mul_distrib],
  refine prod_le_prod' _,
  intros i hi,
  rw mul_comm,
  exact double_factorial_inequality
end
