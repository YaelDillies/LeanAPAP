import Mathlib.MeasureTheory.MeasurableSpace.Defs

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [DiscreteMeasurableSpace α]
  {f : α → β}

-- TODO: Replace in mathlib
lemma Measurable.of_discrete : Measurable f := measurable_discrete _
