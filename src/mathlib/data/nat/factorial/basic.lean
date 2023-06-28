import data.nat.factorial.basic

open_locale nat

namespace nat
variables {n : ℕ}

lemma factorial_two_mul_le : (2 * n)! ≤ (2 * n) ^ n * n! :=
begin
  rw [two_mul, ←factorial_mul_asc_factorial, mul_comm],
  exact mul_le_mul_right' (asc_factorial_le_pow_add _ _) _,
end

end nat
