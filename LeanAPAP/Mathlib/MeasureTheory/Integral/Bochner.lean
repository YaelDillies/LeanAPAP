import Mathlib.MeasureTheory.Integral.Bochner

namespace MeasureTheory
variable {α E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
  {m : MeasurableSpace α} {μ : Measure α} [MeasurableSingletonClass α] [Fintype α]

open Measure

@[simp] lemma integral_count (f : α → E) : ∫ a, f a ∂count = ∑ a, f a := by simp [integral_fintype]

end MeasureTheory
