import Mathlib.Data.Nat.Factorial.Basic

#align_import mathlib.data.nat.factorial.basic

open scoped Nat

namespace Nat
variable {n : ℕ}

lemma factorial_two_mul_le : (2 * n)! ≤ (2 * n) ^ n * n ! := by
  rw [two_mul, ← factorial_mul_asc_factorial, mul_comm]
  exact mul_le_mul_right' (asc_factorial_le_pow_add _ _) _

end Nat
