import Mathlib.Analysis.MeanInequalitiesPow

#align_import mathlib.analysis.mean_inequalities_pow

/-!
## TODO

Generalise to (linearly) ordered semirings?
-/

open Finset

variable {a b : ℝ}

namespace Real

lemma add_sq_le : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have :=
    Real.pow_arith_mean_le_arith_mean_pow_of_even univ ![1 / 2, 1 / 2] ![a, b]
      (by simp [Fin.forall_fin_two]) (by norm_num) even_two
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, sq] at
    this
  linarith

lemma add_pow_le (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a + b) ^ n ≤ 2 ^ (n - 1) * (a ^ n + b ^ n) := by
  cases n
  · simp
  rw [Nat.succ_sub_one, ← div_le_iff']
  simpa using @Real.pow_sum_div_card_le_sum_pow _ univ ![a, b] n (by simp [Fin.forall_fin_two, *])
  · positivity

end Real
