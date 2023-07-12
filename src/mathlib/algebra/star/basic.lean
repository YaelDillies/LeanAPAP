import algebra.star.basic

instance : star_ring ℕ := star_ring_of_comm
instance : has_trivial_star ℕ := ⟨λ _, rfl⟩

instance : star_ring ℚ := star_ring_of_comm
instance : has_trivial_star ℚ := ⟨λ _, rfl⟩

instance star_add_monoid.to_nat_star_module {α} [add_comm_monoid α] [star_add_monoid α] :
  star_module ℕ α :=
⟨λ n a, by rw [star_nsmul, star_trivial n]⟩
