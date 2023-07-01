import data.finset.card

namespace finset
variables {α R : Type*} [add_group_with_one R] [decidable_eq α] {s t : finset α}

lemma cast_card_sdiff (h : s ⊆ t) : ((t \ s).card : R) = t.card - s.card :=
by rw [card_sdiff h, nat.cast_sub (card_mono h)]

end finset
