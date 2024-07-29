import Mathlib.Order.LiminfLimsup

namespace Filter
variable {α β : Type*} [CompleteLattice α]

@[simp] lemma limsup_top (u : β → α) : limsup u ⊤ = ⨆ i, u i := by simp [limsup_eq_iInf_iSup]
@[simp] lemma liminf_top (u : β → α) : liminf u ⊤ = ⨅ i, u i := by simp [liminf_eq_iSup_iInf]

end Filter
