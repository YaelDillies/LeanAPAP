import Mathlib.Data.Finset.Powerset

/-!
## TODO

Rename `finset.powersetCard_empty` to `finset.powersetCard_eq_empty`
-/

namespace Finset
variable {α : Type*}

attribute [simp] mem_powersetCard

lemma powersetCard_empty_subsingleton (n : ℕ) :
    (powersetCard n (∅ : Finset α) : Set $ Finset α).Subsingleton := by
  simp [Set.Subsingleton, subset_empty]

end Finset
