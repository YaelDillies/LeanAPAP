import Mathbin.Algebra.Star.SelfAdjoint
import Mathbin.Algebra.Star.Pi

#align_import mathlib.algebra.star.self_adjoint

open Function

open scoped ComplexConjugate

attribute [simp] isSelfAdjoint_zero isSelfAdjoint_one

section CommSemiring

variable {α : Type _} [CommSemiring α] [StarRing α] {a : α}

theorem IsSelfAdjoint.conj_eq (ha : IsSelfAdjoint a) : conj a = a :=
  ha.star_eq

end CommSemiring

namespace Pi

variable {ι : Type _} {α : ι → Type _} [∀ i, Star (α i)] {f : ∀ i, α i}

protected theorem isSelfAdjoint : IsSelfAdjoint f ↔ ∀ i, IsSelfAdjoint (f i) :=
  funext_iff

alias ⟨_root_.is_self_adjoint.apply, _⟩ := Pi.isSelfAdjoint

end Pi

