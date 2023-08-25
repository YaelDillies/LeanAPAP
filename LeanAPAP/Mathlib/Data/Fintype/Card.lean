import Mathlib.Data.Fintype.Card

#align_import mathlib.data.fintype.card

namespace Fintype

@[simp]
lemma card_multiplicative (α : Type*) [Fintype α] : card (Multiplicative α) = card α := rfl

@[simp]
lemma card_additive (α : Type*) [Fintype α] : card (Additive α) = card α := rfl

end Fintype
