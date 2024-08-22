import Mathlib.Data.NNReal.Basic

open Set

namespace NNReal
variable {ι : Sort*} {f : ι → ℝ≥0}

attribute [simp] coe_sum

@[simp] lemma iSup_eq_zero (hf : BddAbove (range f)) : ⨆ i, f i = 0 ↔ ∀ i, f i = 0 := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp [← bot_eq_zero', ← le_bot_iff, ciSup_le_iff hf]

end NNReal
