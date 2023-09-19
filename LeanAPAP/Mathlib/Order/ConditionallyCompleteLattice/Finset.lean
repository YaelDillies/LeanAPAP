import Mathlib.Order.ConditionallyCompleteLattice.Finset

variable {α β : Type*}

namespace Finset
variable [Fintype α] [Nonempty α] [ConditionallyCompleteLattice β]

lemma sup'_univ_eq_csupr (f : α → β) : univ.sup' univ_nonempty f = ⨆ i, f i := by
  simp [sup'_eq_csSup_image, iSup]

lemma inf'_univ_eq_cinfi (f : α → β) : univ.inf' univ_nonempty f = ⨅ i, f i := by
  simp [inf'_eq_csInf_image, iInf]

end Finset
