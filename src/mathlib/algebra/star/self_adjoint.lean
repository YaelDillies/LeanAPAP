import algebra.star.self_adjoint
import algebra.star.pi

open function
open_locale complex_conjugate

attribute [simp] is_self_adjoint_zero is_self_adjoint_one

section comm_semiring
variables {α : Type*} [comm_semiring α] [star_ring α] {a : α}

lemma is_self_adjoint.conj_eq (ha : is_self_adjoint a) : conj a = a := ha.star_eq

end comm_semiring

namespace pi
variables {ι : Type*} {α : ι → Type*} [Π i, has_star (α i)] {f : Π i, α i}

protected lemma is_self_adjoint : is_self_adjoint f ↔ ∀ i, is_self_adjoint (f i) := funext_iff

alias pi.is_self_adjoint ↔ _root_.is_self_adjoint.apply _

end pi
