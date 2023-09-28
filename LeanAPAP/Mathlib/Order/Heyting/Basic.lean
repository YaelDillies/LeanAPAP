import Mathlib.Order.BooleanAlgebra

section
variable {α : Type*} [GeneralizedHeytingAlgebra α] {a b : α}

@[simp] lemma himp_eq_himp : b ⇨ a = a ⇨ b ↔ a = b := by simp [le_antisymm_iff]
lemma himp_ne_himp : b ⇨ a ≠ a ⇨ b ↔ a ≠ b := himp_eq_himp.not

end

section
variable {α : Type*} [GeneralizedCoheytingAlgebra α] {a b : α}

@[simp] lemma sdiff_eq_sdiff : a \ b = b \ a ↔ a = b := by simp [le_antisymm_iff]
lemma sdiff_ne_sdiff : a \ b ≠ b \ a ↔ a ≠ b := sdiff_eq_sdiff.not

end
