import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace MeasureTheory.Measure
variable {ι α : Type*} {mα : MeasurableSpace α} {f : ι → Measure α}

@[simp] lemma sum_eq_zero : sum f = 0 ↔ ∀ i, f i = 0 := by
  simp (config := { contextual := true }) [Measure.ext_iff, forall_swap (α := ι)]

end MeasureTheory.Measure
