import Mathlib.Algebra.Hom.Group
import Mathlib.Tactic.Coe

namespace AddMonoid.End
variable {α : Type*} [AddZeroClass α] {f g : AddMonoid.End α}

@[ext] lemma ext (h : ∀ a, f a = g a) : f = g := AddMonoidHom.ext h

end AddMonoid.End

namespace Monoid.End
variable {α : Type*} [MulOneClass α] {f g : Monoid.End α}

@[to_additive existing (attr := ext)] lemma ext (h : ∀ a, f a = g a) : f = g := MonoidHom.ext h

end Monoid.End
