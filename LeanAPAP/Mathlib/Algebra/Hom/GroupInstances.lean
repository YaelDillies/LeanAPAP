import Mathbin.Algebra.Hom.GroupInstances
import Mathbin.Data.Pi.Algebra

#align_import mathlib.algebra.hom.group_instances

variable {α β : Type _} [MulOneClass α] [CommMonoid β]

namespace MonoidHom

--TODO: Rename `monoid_hom.coe_pow` to `monoid.End.coe_pow`
@[simp, norm_cast, to_additive]
theorem coe_pow' (n : ℕ) (f : α →* β) : ⇑(f ^ n) = f ^ n :=
  rfl

@[to_additive]
theorem pow_apply (n : ℕ) (f : α →* β) (a : α) : (f ^ n) a = f a ^ n :=
  rfl

end MonoidHom

