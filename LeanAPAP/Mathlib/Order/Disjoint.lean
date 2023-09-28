import Mathlib.Order.Disjoint

section OrderBot
variable {α : Type*} [PartialOrder α] [OrderBot α] {a b : α}

lemma Disjoint.eq_iff (hab : Disjoint a b) : a = b ↔ a = ⊥ ∧ b = ⊥ := by aesop
lemma Disjoint.ne_iff (hab : Disjoint a b) : a ≠ b ↔ a ≠ ⊥ ∨ b ≠ ⊥ :=
  hab.eq_iff.not.trans not_and_or

end OrderBot

section OrderTop
variable {α : Type*} [PartialOrder α] [OrderTop α] {a b : α}

lemma Codisjoint.eq_iff (hab : Codisjoint a b) : a = b ↔ a = ⊤ ∧ b = ⊤ := by aesop
lemma Codisjoint.ne_iff (hab : Codisjoint a b) : a ≠ b ↔ a ≠ ⊤ ∨ b ≠ ⊤ :=
  hab.eq_iff.not.trans not_and_or

end OrderTop
