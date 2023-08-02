import data.fintype.basic

variables {α : Type*} [fintype α] [decidable_eq α]

namespace finset

@[simp] lemma filter_mem_univ (s : finset α) : univ.filter (∈ s) = s :=
by simp [filter_mem_eq_inter]

-- @[simp] --TODO: Unsimp `finset.univ_unique`
lemma singleton_eq_univ [subsingleton α] (a : α) : ({a} : finset α) = univ := by ext; simp

end finset
