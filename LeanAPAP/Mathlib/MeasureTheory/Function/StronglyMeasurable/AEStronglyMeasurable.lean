import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import LeanAPAP.Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

namespace MeasureTheory
variable {α β : Type*} {m m₀ : MeasurableSpace α} [TopologicalSpace β] [Countable α]
  [MeasurableSingletonClass α] {f : α → β} {μ : Measure α}

-- TODO: Replace, make args implicit
attribute [nontriviality] AEStronglyMeasurable.of_subsingleton_cod
  AEStronglyMeasurable.of_subsingleton_dom

-- TODO: Replace `StronglyMeasurable.of_finite`
lemma AEStronglyMeasurable.of_discrete : AEStronglyMeasurable f μ :=
  StronglyMeasurable.of_discrete.aestronglyMeasurable
