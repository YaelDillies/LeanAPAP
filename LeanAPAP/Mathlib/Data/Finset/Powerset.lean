import Mathlib.Data.Finset.Powerset

/-!
## TODO

Rename `finset.powersetLen_empty` to `finset.powersetLen_eq_empty`
-/

namespace Finset
variable {α : Type*}

attribute [simp] mem_powersetLen

lemma powersetLen_empty_subsingleton (n : ℕ) :
    (powersetLen n (∅ : Finset α) : Set $ Finset α).Subsingleton := by
  simp [Set.Subsingleton, subset_empty]

end Finset
