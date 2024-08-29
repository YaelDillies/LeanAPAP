import Mathlib.Order.ConditionallyCompleteLattice.Basic

variable {α β : Type*} [CompleteLattice β] {S : Set α} {f : α → β}

lemma iInf_lt_top : ⨅ i ∈ S, f i < ⊤ ↔ ∃ i ∈ S, f i < ⊤ := by simp [lt_top_iff_ne_top]
