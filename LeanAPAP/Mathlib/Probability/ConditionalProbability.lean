import Mathlib.Probability.ConditionalProbability

open ENNReal MeasureTheory MeasureTheory.Measure MeasurableSpace Set

variable {Ω Ω' α : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} (μ : Measure Ω)
  {s t : Set Ω}

namespace ProbabilityTheory

@[simp] lemma cond_apply_self (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) : μ[|s] s = 1 := by
  simpa [cond] using ENNReal.inv_mul_cancel hs₀ hs

end ProbabilityTheory
