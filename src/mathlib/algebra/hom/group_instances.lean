import algebra.hom.group_instances
import data.pi.algebra

variables {α β : Type*} [mul_one_class α] [comm_monoid β]

namespace monoid_hom

--TODO: Rename `monoid_hom.coe_pow` to `monoid.End.coe_pow`
@[simp, norm_cast, to_additive] lemma coe_pow' (n : ℕ) (f : α →* β) : ⇑(f ^ n) = f ^ n := rfl

@[to_additive] lemma pow_apply (n : ℕ) (f : α →* β) (a : α) : (f ^ n) a = f a ^ n := rfl

end monoid_hom
