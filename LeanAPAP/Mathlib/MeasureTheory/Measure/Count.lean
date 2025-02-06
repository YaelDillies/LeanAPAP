import Mathlib.MeasureTheory.Measure.Count
import LeanAPAP.Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace MeasureTheory.Measure
variable {α : Type*} [MeasurableSpace α]{s : Set α}

lemma count_apply' (hs : MeasurableSet s) : count s = s.encard := by
  simp [count_apply hs, ENNReal.tsum_const, Set.encard]
