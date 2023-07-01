import algebra.group_power.order

variables {α : Type*} [ordered_semiring α] {a b : α} {n : ℕ}

lemma pow_add_pow_le' (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ n + b ^ n ≤ 2 * (a + b) ^ n :=
begin
  rw two_mul,
  exact add_le_add (pow_le_pow_of_le_left ha (le_add_of_nonneg_right hb) _)
    (pow_le_pow_of_le_left hb (le_add_of_nonneg_left ha) _),
end
