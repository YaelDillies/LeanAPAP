import analysis.mean_inequalities_pow

/-!
## TODO

Generalise to (linearly) ordered semirings?
-/

open finset

variables {a b : ℝ}

namespace real

lemma add_sq_le : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) :=
begin
  have := real.pow_arith_mean_le_arith_mean_pow_of_even univ ![1/2, 1/2] ![a, b]
    (by simp [fin.forall_fin_two]) (by norm_num) even_two,
  simp only [fin.sum_univ_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons, sq]
    at this,
  linarith
end

lemma add_pow_le (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) : (a + b) ^ n ≤ 2 ^ (n - 1) * (a ^ n + b ^ n) :=
begin
  cases n,
  { simp },
  rw [nat.succ_sub_one, ←div_le_iff'],
  simpa using @real.pow_sum_div_card_le_sum_pow _ univ ![a, b] n (by simp [fin.forall_fin_two, *]),
  { positivity }
end

end real
