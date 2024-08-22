import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import LeanAPAP.Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [DiscreteMeasurableSpace α]
  {μ : Measure α} {f : α → β}

lemma AEMeasurable.of_discrete : AEMeasurable f μ := Measurable.of_discrete.aemeasurable
