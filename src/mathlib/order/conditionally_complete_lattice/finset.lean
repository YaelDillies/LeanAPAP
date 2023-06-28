import order.conditionally_complete_lattice.finset

variables {α β : Type*}

namespace finset
variables [fintype α] [nonempty α] [conditionally_complete_lattice β]

lemma sup'_univ_eq_csupr (f : α → β) : univ.sup' univ_nonempty f = ⨆ i, f i :=
by simp [sup'_eq_cSup_image, supr]

lemma inf'_univ_eq_cinfi (f : α → β) : univ.inf' univ_nonempty f = ⨅ i, f i :=
by simp [inf'_eq_cInf_image, infi]

end finset
