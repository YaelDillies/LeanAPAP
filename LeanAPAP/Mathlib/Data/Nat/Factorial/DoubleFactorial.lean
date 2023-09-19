import Mathlib.Data.Nat.Factorial.DoubleFactorial

open scoped Nat

namespace Nat
variable {n : ℕ}

lemma doubleFactorial_pos : ∀ {n}, 0 < n‼
  | 0 => zero_lt_one
  | 1 => zero_lt_one
  | _n + 2 => mul_pos (succ_pos _) doubleFactorial_pos

lemma doubleFactorial_le_factorial : n‼ ≤ n ! := by
  cases n
  · rfl
  · rw [factorial_eq_mul_doubleFactorial]
    exact le_mul_of_pos_right doubleFactorial_pos

end Nat
