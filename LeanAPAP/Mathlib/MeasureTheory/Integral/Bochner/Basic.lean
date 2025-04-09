import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# TODO

Rename
* `integral_countable'` → `integral_countable`
* `integral_countable` → `setIntegral_countable`
-/
namespace MeasureTheory
variable {α E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
  {m : MeasurableSpace α} {μ : Measure α} [MeasurableSingletonClass α] [Countable α] {f : α → E}

open Measure

@[simp]
lemma integral_count' (hf : Integrable f .count) : ∫ a, f a ∂count = ∑' a, f a := by
  simp [integral_countable' hf]

end MeasureTheory
