import Mathlib.GroupTheory.GroupAction.Group

open Function

section GroupWithZero
variable {α : Type*} (β : Type*)
variable [Preorder α] [Preorder β] [GroupWithZero α] [Zero β] [MulAction α β] {a : α}

/-- Left scalar multiplication as an order isomorphism. -/
@[simps] def Equiv.smulRight (ha : a ≠ 0) : β ≃ β where
  toFun b := a • b
  invFun b := a⁻¹ • b
  left_inv := inv_smul_smul₀ ha
  right_inv := smul_inv_smul₀ ha

lemma smul_right_injective₀ (ha : a ≠ 0) : Injective (a • · : β → β) :=
  (Equiv.smulRight _ ha).injective

end GroupWithZero
