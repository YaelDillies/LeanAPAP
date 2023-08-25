import Mathlib.Algebra.Hom.GroupInstances
import Mathlib.Data.Pi.Algebra

#align_import mathlib.algebra.hom.group_instances

variable {α β : Type*} [MulOneClass α] [CommMonoid β]

namespace MonoidHom

--TODO: Rename `monoid_hom.coe_pow` to `monoid.End.coe_pow`
@[simp, norm_cast, to_additive]
lemma coe_pow' (n : ℕ) (f : α →* β) : ⇑(f ^ n) = f ^ n := rfl

@[to_additive]
lemma pow_apply (n : ℕ) (f : α →* β) (a : α) : (f ^ n) a = f a ^ n := rfl

end MonoidHom
