import Mathlib.Data.Set.Card

open Function

namespace Set
variable {α β : Type*} {f : α → β}

lemma encard_preimage_of_bijective (hf : Bijective f) (t : Set β) : (f ⁻¹' t).encard = t.encard :=
  encard_preimage_of_injective_subset_range hf.injective (by simp [hf.surjective.range_eq])
