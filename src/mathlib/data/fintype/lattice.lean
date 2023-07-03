import data.fintype.lattice

namespace finset

lemma mem_inf {α β} [fintype β] [decidable_eq β] {s : finset α} {f : α → finset β} {x : β} :
  x ∈ s.inf f ↔ ∀ v ∈ s, x ∈ f v :=
by induction s using finset.cons_induction with a s ha ih; simp [*]

end finset
