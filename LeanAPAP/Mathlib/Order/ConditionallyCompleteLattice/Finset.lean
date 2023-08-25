import Mathbin.Order.ConditionallyCompleteLattice.Finset

#align_import mathlib.order.conditionally_complete_lattice.finset

variable {α β : Type _}

namespace Finset

variable [Fintype α] [Nonempty α] [ConditionallyCompleteLattice β]

theorem sup'_univ_eq_csupr (f : α → β) : univ.sup' univ_nonempty f = ⨆ i, f i := by
  simp [sup'_eq_cSup_image, iSup]

theorem inf'_univ_eq_cinfi (f : α → β) : univ.inf' univ_nonempty f = ⨅ i, f i := by
  simp [inf'_eq_cInf_image, iInf]

end Finset

