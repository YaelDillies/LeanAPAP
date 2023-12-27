import Mathlib.Data.Fintype.Basic

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace Finset

@[simp]
lemma filter_mem_univ (s : Finset α) : univ.filter (· ∈ s) = s := by simp [filter_mem_eq_inter]

-- TODO: Unsimp `Finset.univ_unique`

end Finset
