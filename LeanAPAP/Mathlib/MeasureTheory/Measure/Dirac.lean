import Mathlib.MeasureTheory.Measure.Dirac

open Set

namespace MeasureTheory.Measure
variable {α : Type*} {mα : MeasurableSpace α}

@[simp] lemma dirac_ne_zero (a : α) : dirac a ≠ 0 :=
  fun h ↦ by simpa [h] using dirac_apply_of_mem (mem_univ a)

end MeasureTheory.Measure
