import Mathlib.Probability.UniformOn

namespace ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {s : Set Ω}

@[simp] lemma uniformOn_eq_zero : uniformOn s = 0 ↔ s.Infinite ∨ s = ∅ := by simp [uniformOn]
@[simp] lemma uniformOn_eq_zero' (hs : s.Finite) : uniformOn s = 0 ↔ s = ∅ := by
  simp [uniformOn, hs]

end ProbabilityTheory
