import Mathlib.Probability.ConditionalProbability

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory
variable {Ω Ω' α : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {s t : Set Ω}

-- TODO: Replace `cond_eq_zero`
@[simp] lemma cond_eq_zero' : μ[|s] = 0 ↔ μ s = ∞ ∨ μ s = 0 := by simp [cond]

end ProbabilityTheory
