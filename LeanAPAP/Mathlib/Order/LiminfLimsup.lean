import Mathlib.Order.LiminfLimsup

open Set

namespace Filter
variable {α β : Type*} [ConditionallyCompleteLattice α] {u : β → α} {s : Set α}

lemma limsup_top_eq_ciSup [Nonempty β] (hu : BddAbove (range u)) : limsup u ⊤ = ⨆ i, u i := by
  rw [limsup, map_top, limsSup_principal hu (range_nonempty _), sSup_range]

lemma liminf_top_eq_ciInf [Nonempty β] (hu : BddBelow (range u)) : liminf u ⊤ = ⨅ i, u i := by
  rw [liminf, map_top, limsInf_principal hu (range_nonempty _), sInf_range]

end Filter
