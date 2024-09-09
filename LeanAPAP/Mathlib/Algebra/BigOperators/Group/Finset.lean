import Mathlib.Algebra.BigOperators.Group.Finset

namespace Fintype
variable {ι α : Type*} [Fintype ι] [CommMonoid α] [DecidableEq ι]

@[to_additive]
lemma prod_ite_mem (s : Finset ι) (f : ι → α) : ∏ i, (if i ∈ s then f i else 1) = ∏ i ∈ s, f i := by
  simp

end Fintype
