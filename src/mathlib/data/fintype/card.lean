import data.fintype.card

namespace fintype

@[simp] lemma card_multiplicative (α : Type*) [fintype α] : card (multiplicative α) = card α := rfl
@[simp] lemma card_additive (α : Type*) [fintype α] : card (additive α) = card α := rfl

end fintype
