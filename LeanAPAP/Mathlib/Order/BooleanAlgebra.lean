import Mathlib.Order.BooleanAlgebra
import LeanAPAP.Mathlib.Order.Disjoint

section
variable {α : Type*} [GeneralizedBooleanAlgebra α] {a b : α}

@[simp] lemma sdiff_eq_right : a \ b = b ↔ a = ⊥ ∧ b = ⊥ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨h, rfl⟩ := disjoint_sdiff_self_left.eq_iff.1 h
    simpa using h
  · rintro ⟨rfl, rfl⟩
    exact bot_sdiff

lemma sdiff_ne_right : a \ b ≠ b ↔ a ≠ ⊥ ∨ b ≠ ⊥ := sdiff_eq_right.not.trans not_and_or

end
