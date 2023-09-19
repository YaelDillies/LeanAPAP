import Mathlib.Data.Fintype.Card

namespace Fintype

@[simp] lemma card_multiplicative (α : Type*) [Fintype α] : card (Multiplicative α) = card α :=
  Finset.card_map _

@[simp] lemma card_additive (α : Type*) [Fintype α] : card (Additive α) = card α :=
  Finset.card_map _

end Fintype
