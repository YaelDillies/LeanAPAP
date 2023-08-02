import data.finset.basic

namespace finset
variables {α : Type*}

lemma filter_comm (s : finset α) (p q : α → Prop) [decidable_pred p] [decidable_pred q] :
  (s.filter p).filter q = (s.filter q).filter p := by simp_rw [filter_filter, and_comm]

@[simp] lemma filter_const (s : finset α) (p : Prop) [decidable p] :
  s.filter (λ a, p) = if p then s else ∅ :=
by split_ifs; simp [*]

end finset
