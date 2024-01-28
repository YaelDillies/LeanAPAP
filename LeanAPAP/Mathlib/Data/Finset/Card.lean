import Mathlib.Data.Finset.Card

namespace Finset
variable {α : Type*} [DecidableEq α] {s t : Finset α} {γ : Type*} [Ring γ]

-- TODO: does this work for anything more general than Ring?
lemma card_inter_eq : ((s ∩ t).card : γ) = s.card + t.card - (s ∪ t).card := by
  rw [eq_sub_iff_add_eq, ←Nat.cast_add, Finset.card_inter_add_card_union, Nat.cast_add]

lemma card_union_eq' : ((s ∪ t).card : γ) = s.card + t.card - (s ∩ t).card := by
  rw [eq_sub_iff_add_eq, ←Nat.cast_add, Finset.card_union_add_card_inter, Nat.cast_add]

end Finset
