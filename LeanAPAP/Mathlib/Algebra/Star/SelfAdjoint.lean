import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.Pi

#align_import mathlib.algebra.star.self_adjoint

open Function

open scoped ComplexConjugate

attribute [simp] isSelfAdjoint_zero isSelfAdjoint_one

section CommSemiring
variable {α : Type*} [CommSemiring α] [StarRing α] {a : α}

lemma IsSelfAdjoint.conj_eq (ha : IsSelfAdjoint a) : conj a = a :=
  ha.star_eq

end CommSemiring

namespace Pi
variable {ι : Type*} {α : ι → Type*} [∀ i, Star (α i)] {f : ∀ i, α i}

protected lemma isSelfAdjoint : IsSelfAdjoint f ↔ ∀ i, IsSelfAdjoint (f i) :=
  funext_iff

alias ⟨_root_.is_self_adjoint.apply, _⟩ := Pi.isSelfAdjoint

end Pi
