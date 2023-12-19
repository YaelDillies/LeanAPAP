import Mathlib.Data.Finset.Basic

namespace Finset
variable {α : Type*} {s : Finset α} {a : α}

attribute [pp_dot] Finset.Nonempty

@[norm_cast]
lemma coe_subset_singleton : (s : Set α) ⊆ {a} ↔ s ⊆ {a} := by rw [←coe_subset, coe_singleton]

@[norm_cast]
lemma singleton_subset_coe : {a} ⊆ (s : Set α) ↔ {a} ⊆ s := by rw [←coe_subset, coe_singleton]

end Finset
