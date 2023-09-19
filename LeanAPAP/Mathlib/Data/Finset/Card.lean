import Mathlib.Data.Finset.Card

namespace Finset
variable {α R : Type*} [AddGroupWithOne R] [DecidableEq α] {s t : Finset α}

lemma cast_card_sdiff (h : s ⊆ t) : ((t \ s).card : R) = t.card - s.card := by
  rw [card_sdiff h, Nat.cast_sub (card_mono h)]

end Finset
