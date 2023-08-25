import Mathbin.Data.Finset.Powerset

#align_import mathlib.data.finset.powerset

/-!
## TODO

Rename `finset.powerset_len_empty` to `finset.powerset_len_eq_empty`
-/


namespace Finset

variable {α : Type _}

attribute [simp] mem_powerset_len

theorem powersetLen_empty_subsingleton (n : ℕ) :
    (powersetLen n (∅ : Finset α) : Set <| Finset α).Subsingleton := by
  simp [Set.Subsingleton, subset_empty]

end Finset

