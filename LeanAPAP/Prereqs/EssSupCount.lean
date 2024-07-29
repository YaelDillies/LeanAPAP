import LeanAPAP.Mathlib.MeasureTheory.Function.EssSup
import LeanAPAP.Mathlib.MeasureTheory.Measure.Count
import LeanAPAP.Mathlib.MeasureTheory.OuterMeasure.AE
import LeanAPAP.Mathlib.Order.LiminfLimsup

open Filter MeasureTheory

variable {α β : Type*} [CompleteLinearOrder β] {m : MeasurableSpace α} [MeasurableSingletonClass α]
  {μ : Measure α}

@[simp] lemma essSup_count (f : α → β) : essSup f .count = ⨆ i, f i :=
  essSup_eq_iSup (by simp) _

@[simp] lemma essInf_count (f : α → β) : essInf f .count = ⨅ i, f i :=
  essInf_eq_iInf (by simp) _
