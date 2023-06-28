import data.nat.factorial.double_factorial

open_locale nat

namespace nat
variables {n : ℕ}

lemma double_factorial_pos : ∀ {n}, 0 <n‼
| 0 := zero_lt_one
| 1 := zero_lt_one
| (n + 2) := mul_pos (succ_pos _) double_factorial_pos

lemma double_factorial_le_factorial : n‼ ≤ n! :=
begin
  cases n,
  { refl },
  { rw factorial_eq_mul_double_factorial,
    exact le_mul_of_pos_right double_factorial_pos }
end

end nat
