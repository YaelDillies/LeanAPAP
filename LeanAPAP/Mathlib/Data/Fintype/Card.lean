import Mathbin.Data.Fintype.Card

#align_import mathlib.data.fintype.card

namespace Fintype

@[simp]
theorem card_multiplicative (α : Type _) [Fintype α] : card (Multiplicative α) = card α :=
  rfl

@[simp]
theorem card_additive (α : Type _) [Fintype α] : card (Additive α) = card α :=
  rfl

end Fintype

