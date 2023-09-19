import Mathlib.Data.Nat.Factorial.Basic

open scoped Nat

namespace Nat
variable {n : ℕ}

lemma factorial_two_mul_le : (2 * n)! ≤ (2 * n) ^ n * n ! := by
  rw [two_mul, ←factorial_mul_ascFactorial, mul_comm]
  exact mul_le_mul_right' (ascFactorial_le_pow_add _ _) _

end Nat
