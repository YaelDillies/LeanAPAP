import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Combinatorics.Enumerative.DoubleCounting

open Function
open scoped BigOperators

namespace Finset
variable {R α β : Type*}

section OrderedSemiring
variable [OrderedSemiring R] (r : α → β → Prop) {s : Finset α} {t : Finset β}
  (a a' : α) (b b' : β) [DecidablePred (r a)] [∀ a, Decidable (r a b)] {m n : R}

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of edges while the RHS
is an upper bound. -/
theorem card_nsmul_le_card_nsmul [∀ a b, Decidable (r a b)]
    (hm : ∀ a ∈ s, m ≤ (t.bipartiteAbove r a).card)
    (hn : ∀ b ∈ t, (s.bipartiteBelow r b).card ≤ n) : s.card • m ≤ t.card • n :=
  calc
    _ ≤ ∑ a in s, ((t.bipartiteAbove r a).card : R) := s.card_nsmul_le_sum _ _ hm
    _ = ∑ b in t, ((s.bipartiteBelow r b).card : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ ≤ _ := t.sum_le_card_nsmul _ _ hn

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of edges while the RHS
is an upper bound. -/
theorem card_nsmul_le_card_nsmul' [∀ a b, Decidable (r a b)]
    (hn : ∀ b ∈ t, n ≤ (s.bipartiteBelow r b).card)
    (hm : ∀ a ∈ s, (t.bipartiteAbove r a).card ≤ m) : t.card • n ≤ s.card • m :=
  card_nsmul_le_card_nsmul (swap r) hn hm

end OrderedSemiring

section StrictOrderedSemiring
variable [StrictOrderedSemiring R] (r : α → β → Prop) {s : Finset α} {t : Finset β}
  (a a' : α) (b b' : β) [DecidablePred (r a)] [∀ a, Decidable (r a b)] {m n : R}

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a strict lower bound on the number of edges while
the RHS is an upper bound. -/
theorem card_nsmul_lt_card_nsmul_of_lt_of_le [∀ a b, Decidable (r a b)] (hs : s.Nonempty)
    (hm : ∀ a ∈ s, m < (t.bipartiteAbove r a).card)
    (hn : ∀ b ∈ t, (s.bipartiteBelow r b).card ≤ n) : s.card • m < t.card • n :=
  calc
    _ = ∑ _a ∈ s, m := by rw [sum_const]
    _ < ∑ a ∈ s, ((t.bipartiteAbove r a).card : R) := sum_lt_sum_of_nonempty hs hm
    _ = ∑ b in t, ((s.bipartiteBelow r b).card : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ ≤ _ := t.sum_le_card_nsmul _ _ hn

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of edges while the RHS
is a strict upper bound. -/
theorem card_nsmul_lt_card_nsmul_of_le_of_lt [∀ a b, Decidable (r a b)] (ht : t.Nonempty)
    (hm : ∀ a ∈ s, m ≤ (t.bipartiteAbove r a).card)
    (hn : ∀ b ∈ t, (s.bipartiteBelow r b).card < n) : s.card • m < t.card • n :=
  calc
    _ ≤ ∑ a in s, ((t.bipartiteAbove r a).card : R) := s.card_nsmul_le_sum _ _ hm
    _ = ∑ b in t, ((s.bipartiteBelow r b).card : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ < ∑ _b ∈ t, n := sum_lt_sum_of_nonempty ht hn
    _ = _ := sum_const _

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a strict lower bound on the number of edges while
the RHS is an upper bound. -/
theorem card_nsmul_lt_card_nsmul_of_lt_of_le' [∀ a b, Decidable (r a b)] (ht : t.Nonempty)
    (hn : ∀ b ∈ t, n < (s.bipartiteBelow r b).card)
    (hm : ∀ a ∈ s, (t.bipartiteAbove r a).card ≤ m) : t.card • n < s.card • m :=
  card_nsmul_lt_card_nsmul_of_lt_of_le (swap r) ht hn hm

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of edges while the RHS
is a strict upper bound. -/
theorem card_nsmul_lt_card_nsmul_of_le_of_lt' [∀ a b, Decidable (r a b)] (hs : s.Nonempty)
    (hn : ∀ b ∈ t, n ≤ (s.bipartiteBelow r b).card)
    (hm : ∀ a ∈ s, (t.bipartiteAbove r a).card < m) : t.card • n < s.card • m :=
  card_nsmul_lt_card_nsmul_of_le_of_lt (swap r) hs hn hm
  
end StrictOrderedSemiring
end Finset
