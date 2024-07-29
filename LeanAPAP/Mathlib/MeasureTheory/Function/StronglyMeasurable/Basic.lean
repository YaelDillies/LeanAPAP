import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import LeanAPAP.Mathlib.MeasureTheory.OuterMeasure.AE

namespace MeasureTheory
variable {α β : Type*} [TopologicalSpace β] {m : MeasurableSpace α} [DiscreteMeasurableSpace α]
  [Finite α] {f : α → β} {μ : Measure α}

-- TODO: Rename `StronglyMeasurable.of_finite` to `StronglyMeasurable.of_discrete`
lemma AEStronglyMeasurable.of_discrete : AEStronglyMeasurable f μ := ⟨_, .of_finite _, ae_eq_rfl⟩

end MeasureTheory
