import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.GroupTheory.Submonoid.Basic

namespace Submonoid
variable (α : Type*) [MulOneClass α] [Preorder α] [CovariantClass α α (· * ·) (· ≤ ·)] {a : α}

/-- The submonoid of elements greater than `1`. -/
@[to_additive (attr := simps) nonneg "The submonoid of nonnegative elements."]
def oneLe : Submonoid α where
  carrier := {a | 1 ≤ a}
  mul_mem' := one_le_mul
  one_mem' := le_rfl

variable {α}

@[to_additive (attr := simp)] lemma mem_oneLe : a ∈ oneLe α ↔ 1 ≤ a := Iff.rfl

end Submonoid
