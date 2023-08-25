import Mathbin.Algebra.Star.Basic

#align_import mathlib.algebra.star.basic

instance : StarRing ℕ :=
  starRingOfComm

instance : TrivialStar ℕ :=
  ⟨fun _ => rfl⟩

instance : StarRing ℚ :=
  starRingOfComm

instance : TrivialStar ℚ :=
  ⟨fun _ => rfl⟩

instance StarAddMonoid.to_nat_starModule {α} [AddCommMonoid α] [StarAddMonoid α] : StarModule ℕ α :=
  ⟨fun n a => by rw [star_nsmul, star_trivial n]⟩

section CommSemiring

variable {α : Type _} [CommSemiring α] [StarRing α] [TrivialStar α]

open scoped ComplexConjugate

@[simp]
theorem conj_trivial (a : α) : conj a = a :=
  star_trivial _

end CommSemiring

