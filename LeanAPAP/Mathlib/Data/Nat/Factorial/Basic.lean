import Mathlib.Data.Nat.Factorial.Basic

namespace Nat

lemma factorial_le_pow : ∀ n, n ! ≤ n ^ n
  | 0 => le_rfl
  | n + 1 =>
    calc
      _ ≤ (n + 1) * n ^ n := mul_le_mul_left' n.factorial_le_pow _
      _ ≤ (n + 1) * (n + 1) ^ n := mul_le_mul_left' (Nat.pow_le_pow_left n.le_succ _) _
      _ = _ := by rw [pow_succ']

end Nat
