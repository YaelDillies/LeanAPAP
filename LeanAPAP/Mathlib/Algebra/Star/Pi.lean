import Mathbin.Algebra.Star.Pi

#align_import mathlib.algebra.star.pi

open scoped ComplexConjugate

--TODO: This is a hack to help Lean synthesize the instance. It has nothing to do with type
-- dependency. Rather, it seems to be about the `non_unital_semiring` structure on `α`.
instance Function.starRing {ι α : Type _} [CommSemiring α] [StarRing α] : StarRing (ι → α) :=
  Pi.starRing

@[simp]
theorem Pi.conj_apply {ι : Type _} {α : ι → Type _} [∀ i, CommSemiring (α i)] [∀ i, StarRing (α i)]
    (f : ∀ i, α i) (i : ι) : @starRingEnd (∀ i, α i) _ (@Pi.starRing ι α _ _) f i = conj (f i) :=
  rfl

