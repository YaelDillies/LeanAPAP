import Mathlib.Data.Fintype.Basic

#align_import mathlib.data.fintype.basic

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace Finset

@[simp]
lemma filter_mem_univ (s : Finset α) : univ.filterₓ (· ∈ s) = s := by simp [filter_mem_eq_inter]

-- @[simp] --TODO: Unsimp `finset.univ_unique`
lemma singleton_eq_univ [Subsingleton α] (a : α) : ({a} : Finset α) = univ := by ext <;> simp

end Finset
