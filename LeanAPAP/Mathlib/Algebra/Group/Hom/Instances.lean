import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Data.Pi.Algebra

variable {α β : Type*}

attribute [to_additive existing] Monoid.End.instMonoidHomClassEnd
attribute [to_additive existing AddMonoid.End.monoid] Monoid.End.instMonoidEnd

namespace AddMonoid.End
variable [AddZeroClass α]

@[simp, norm_cast] lemma coe_one : ⇑(1 : AddMonoid.End α) = id := rfl

end AddMonoid.End

variable [MulOneClass α] [CommMonoid β]

namespace Monoid.End

@[to_additive (attr := simp, norm_cast) existing AddMonoid.End.coe_one]
lemma coe_one : ⇑(1 : Monoid.End α) = id := rfl

end Monoid.End

namespace AddMonoid.End
variable [AddCommMonoid α]

@[simp, norm_cast] lemma coe_zero : ⇑(0 : AddMonoid.End α) = 0 := rfl

end AddMonoid.End

namespace MonoidHom

--TODO: Rename `monoid_hom.coe_pow` to `monoid.End.coe_pow`
@[to_additive (attr := simp, norm_cast)]
lemma coe_pow' (n : ℕ) (f : α →* β) : ⇑(f ^ n) = (⇑f) ^ n := rfl

@[to_additive]
lemma pow_apply (n : ℕ) (f : α →* β) (a : α) : (f ^ n) a = f a ^ n := rfl

end MonoidHom
