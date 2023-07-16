import data.finset.powerset

/-!
## TODO

Rename `finset.powerset_len_empty` to `finset.powerset_len_eq_empty`
-/

namespace finset
variables {α : Type*}

attribute [simp] mem_powerset_len

lemma powerset_len_empty_subsingleton (n : ℕ) :
  (powerset_len n (∅ : finset α) : set $ finset α).subsingleton :=
by simp [set.subsingleton, subset_empty]

end finset
