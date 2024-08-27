import Mathlib.MeasureTheory.Measure.Typeclasses

namespace MeasureTheory
variable {ι α : Type*} {mα : MeasurableSpace α} {s : Finset ι} {μ : ι → Measure α}
  [∀ i, IsFiniteMeasure (μ i)]

attribute [simp] ENNReal.sum_lt_top

instance : IsFiniteMeasure (∑ i ∈ s, μ i) where measure_univ_lt_top := by simp [measure_lt_top]

instance [Fintype ι] : IsFiniteMeasure (.sum μ) where 
  measure_univ_lt_top := by simp [measure_lt_top]

end MeasureTheory
