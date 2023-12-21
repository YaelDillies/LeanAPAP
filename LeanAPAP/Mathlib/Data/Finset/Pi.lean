import Mathlib.Data.Finset.Pi

namespace Finset
variable {α : Type*} {β : α → Type*} [DecidableEq α] {s : Finset α} {t : ∀ a, Finset (β a)}

lemma pi_nonempty (ht : ∀ a ∈ s, (t a).Nonempty) : (s.pi t).Nonempty := by
  choose x hx using ht
  simp_rw [Finset.Nonempty, mem_pi]
  exact ⟨x, hx⟩

end Finset
