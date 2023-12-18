import Mathlib.Data.Nat.Factorial.Basic

open scoped Nat

namespace Nat
variable {n : ℕ}

lemma factorial_two_mul_le : (2 * n)! ≤ (2 * n) ^ n * n ! := by
  rw [two_mul, ←factorial_mul_ascFactorial, mul_comm]
  exact mul_le_mul_right' (ascFactorial_le_pow_add _ _) _

lemma two_pow_mul_factorial_le_factorial_two_mul : 2 ^ n * n ! ≤ (2 * n) ! := by
  obtain _ | n := n
  · simp
  rw [mul_comm, two_mul]
  calc
    _ ≤ (n + 1)! * (n + 2) ^ (n + 1) := mul_le_mul_left' (Nat.pow_le_pow_left le_add_self _) _
    _ ≤ _ := Nat.factorial_mul_pow_le_factorial

end Nat
