import Mathlib.Algebra.Star.Pi

open scoped ComplexConjugate

-- TODO: Rename `Pi.instStarRingForAllNonUnitalNonAssocSemiringToNonUnitalNonAssocSemiring`
alias Pi.instStarRing := Pi.instStarRingForAllNonUnitalNonAssocSemiringToNonUnitalNonAssocSemiring
--TODO: This is a hack to help Lean synthesize the instance. It has nothing to do with type
-- dependency. Rather, it seems to be about the `NonUnitalSemiring` structure on `α`.
instance Function.instStarRing {ι α : Type*} [CommSemiring α] [StarRing α] : StarRing (ι → α) :=
  Pi.instStarRing

@[simp]
lemma Pi.conj_apply {ι : Type*} {α : ι → Type*} [∀ i, CommSemiring (α i)] [∀ i, StarRing (α i)]
    (f : ∀ i, α i) (i : ι) : conj f i = conj (f i) := rfl
