import algebra.star.basic

instance : star_ring ℕ := star_ring_of_comm
instance : has_trivial_star ℕ := ⟨λ _, rfl⟩

instance : star_ring ℚ := star_ring_of_comm
instance : has_trivial_star ℚ := ⟨λ _, rfl⟩

instance star_add_monoid.to_nat_star_module {α} [add_comm_monoid α] [star_add_monoid α] :
  star_module ℕ α :=
⟨λ n a, by rw [star_nsmul, star_trivial n]⟩


section comm_semiring
variables {α : Type*} [comm_semiring α] [star_ring α] [has_trivial_star α]

open_locale complex_conjugate

@[simp] lemma conj_trivial (a : α) : conj a = a := star_trivial _

end comm_semiring
