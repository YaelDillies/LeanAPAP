import Mathlib.MeasureTheory.Measure.Count
import LeanAPAP.Mathlib.MeasureTheory.Measure.Dirac
import LeanAPAP.Mathlib.MeasureTheory.Measure.MeasureSpace

open Set

namespace MeasureTheory.Measure
variable {α : Type*} {mα : MeasurableSpace α}

@[simp] lemma count_univ [Fintype α] : count (univ : Set α) = Fintype.card α := by
  rw [count_apply .univ]
  refine (tsum_univ 1).trans ?_
  sorry

@[simp] lemma count_ne_zero'' [Nonempty α] : (count : Measure α) ≠ 0 := by simp [count]

end MeasureTheory.Measure
