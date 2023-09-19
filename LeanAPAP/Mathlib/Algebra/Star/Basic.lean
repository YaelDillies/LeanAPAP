import Mathlib.Algebra.Star.Basic

instance Nat.instStarRing : StarRing ℕ := starRingOfComm
instance Rat.instStarRing : StarRing ℚ := starRingOfComm
instance Nat.instTrivialStar : TrivialStar ℕ := ⟨λ _ ↦ rfl⟩
instance Rat.instTrivialStar : TrivialStar ℚ := ⟨λ _ ↦ rfl⟩

instance StarAddMonoid.toStarModuleNat {α} [AddCommMonoid α] [StarAddMonoid α] : StarModule ℕ α :=
  ⟨λ n a ↦ by rw [star_nsmul, star_trivial n]⟩

section CommSemiring
variable {α : Type*} [CommSemiring α] [StarRing α] [TrivialStar α]

open scoped ComplexConjugate

@[simp] lemma conj_trivial (a : α) : conj a = a := star_trivial _

end CommSemiring
