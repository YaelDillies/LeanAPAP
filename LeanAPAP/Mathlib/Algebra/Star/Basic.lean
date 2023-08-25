import Mathlib.Algebra.Star.Basic

#align_import mathlib.algebra.star.basic

instance : StarRing ℕ :=
  starRingOfComm

instance : TrivialStar ℕ :=
  ⟨λ _ => rfl⟩

instance : StarRing ℚ :=
  starRingOfComm

instance : TrivialStar ℚ :=
  ⟨λ _ => rfl⟩

instance StarAddMonoid.to_nat_starModule {α} [AddCommMonoid α] [StarAddMonoid α] : StarModule ℕ α :=
  ⟨λ n a => by rw [star_nsmul, star_trivial n]⟩

section CommSemiring
variable {α : Type*} [CommSemiring α] [StarRing α] [TrivialStar α]

open scoped ComplexConjugate

@[simp]
lemma conj_trivial (a : α) : conj a = a :=
  star_trivial _

end CommSemiring
