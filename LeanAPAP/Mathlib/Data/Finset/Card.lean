import Mathbin.Data.Finset.Card

#align_import mathlib.data.finset.card

namespace Finset

variable {α R : Type _} [AddGroupWithOne R] [DecidableEq α] {s t : Finset α}

theorem cast_card_sdiff (h : s ⊆ t) : ((t \ s).card : R) = t.card - s.card := by
  rw [card_sdiff h, Nat.cast_sub (card_mono h)]

end Finset

