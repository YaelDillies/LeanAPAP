import Mathbin.Data.Finset.Basic

#align_import mathlib.data.finset.basic

namespace Finset

variable {α : Type _}

theorem filter_comm (s : Finset α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    (s.filterₓ p).filterₓ q = (s.filterₓ q).filterₓ p := by simp_rw [filter_filter, and_comm']

@[simp]
theorem filter_const (s : Finset α) (p : Prop) [Decidable p] :
    (s.filterₓ fun a => p) = if p then s else ∅ := by split_ifs <;> simp [*]

end Finset

