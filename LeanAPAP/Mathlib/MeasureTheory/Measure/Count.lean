import LeanAPAP.Mathlib.MeasureTheory.Measure.Typeclasses
import Mathlib.MeasureTheory.Measure.Count

namespace MeasureTheory.Measure
variable {α : Type*} [MeasurableSpace α] {s : Set α}

instance [MeasurableSingletonClass α] [Countable α] : SigmaFinite (.count : Measure α) := by
  simp [sigmaFinite_iff_measure_singleton_lt_top]

end MeasureTheory.Measure
