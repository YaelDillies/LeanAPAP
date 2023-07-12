import group_theory.submonoid.basic
import algebra.order.monoid.lemmas

namespace submonoid
variables (α : Type*) [mul_one_class α] [preorder α] [covariant_class α α (*) (≤)] {a : α}

/-- The submonoid of elements greater than `1`. -/
@[to_additive "The submonoid of nonnegative elements.", simps] def one_le : submonoid α :=
{ carrier := {a | 1 ≤ a},
  mul_mem' := λ _ _, one_le_mul,
  one_mem' := le_rfl }

variables {α}

@[simp, to_additive] lemma mem_one_le : a ∈ one_le α ↔ 1 ≤ a := iff.rfl

end submonoid
