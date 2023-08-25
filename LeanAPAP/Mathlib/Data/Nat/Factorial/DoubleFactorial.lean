import Mathlib.Data.Nat.Factorial.DoubleFactorial

#align_import mathlib.data.nat.factorial.double_factorial

open scoped Nat

namespace Nat
variable {n : ℕ}

lemma doubleFactorial_pos : ∀ {n}, 0 < n‼
  | 0 => zero_lt_one
  | 1 => zero_lt_one
  | n + 2 => mul_pos (succ_pos _) double_factorial_pos

lemma doubleFactorial_le_factorial : n‼ ≤ n ! := by
  cases n
  · rfl
  · rw [factorial_eq_mul_double_factorial]
    exact le_mul_of_pos_right double_factorial_pos

end Nat
