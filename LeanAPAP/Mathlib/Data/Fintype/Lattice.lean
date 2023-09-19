import Mathlib.Data.Fintype.Lattice

namespace Finset

lemma mem_inf {α β} [Fintype β] [DecidableEq β] {s : Finset α} {f : α → Finset β} {x : β} :
    x ∈ s.inf f ↔ ∀ v ∈ s, x ∈ f v := by
  induction' s using Finset.cons_induction with a s ha ih <;> simp [*]

end Finset
