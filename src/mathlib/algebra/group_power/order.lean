import algebra.group_power.order

variables {α : Type*}

section ordered_semiring
variables [ordered_semiring α] {a b : α} {n : ℕ}

lemma pow_add_pow_le' (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ n + b ^ n ≤ 2 * (a + b) ^ n :=
begin
  rw two_mul,
  exact add_le_add (pow_le_pow_of_le_left ha (le_add_of_nonneg_right hb) _)
    (pow_le_pow_of_le_left hb (le_add_of_nonneg_left ha) _),
end

end ordered_semiring

section linear_ordered_semiring
variables [linear_ordered_semiring α] {a : α} {n : ℕ}

lemma pow_eq_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 :=
by simp only [le_antisymm_iff, pow_le_one_iff_of_nonneg ha hn, one_le_pow_iff_of_nonneg ha hn]

end linear_ordered_semiring
