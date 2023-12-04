import Mathlib.Data.Fintype.Basic

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace Finset

@[simp]
lemma filter_mem_univ (s : Finset α) : univ.filter (· ∈ s) = s := by simp [filter_mem_eq_inter]

-- @[simp] --TODO: Unsimp `finset.univ_unique`
lemma singleton_eq_univ [Subsingleton α] (a : α) : ({a} : Finset α) = univ := by
  ext b; simp [Subsingleton.elim a b]

end Finset

instance {s : Set α} [DecidablePred (· ∈ s)] : Decidable s.Subsingleton :=
  decidable_of_iff (∀ a ∈ s, ∀ b ∈ s, a = b) Iff.rfl
