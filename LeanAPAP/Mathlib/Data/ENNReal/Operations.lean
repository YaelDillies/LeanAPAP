import Mathlib.Data.ENNReal.Operations

namespace ENNReal
variable {α : Type*} {s : Finset α} {f : α → ℝ≥0∞}

lemma sum_ne_top : ∑ a ∈ s, f a ≠ ∞ ↔ ∀ a ∈ s, f a ≠ ⊤ := by
  simpa [lt_top_iff_ne_top] using sum_lt_top_iff

end ENNReal
