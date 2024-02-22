import Mathlib.GroupTheory.Submonoid.Operations

namespace Submonoid
variable {M : Type*} [MulOneClass M] {S : Submonoid M}

@[to_additive (attr := simp)]
lemma mk_eq_one {a : M} {ha} : (⟨a, ha⟩ : S) = 1 ↔ a = 1 := by simp [← SetLike.coe_eq_coe]

end Submonoid
