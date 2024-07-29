import Mathlib.MeasureTheory.Function.EssSup
import LeanAPAP.Mathlib.MeasureTheory.OuterMeasure.AE
import LeanAPAP.Mathlib.Order.LiminfLimsup

open Filter MeasureTheory

variable {α β : Type*} [CompleteLinearOrder β] {m : MeasurableSpace α} {μ : Measure α}

lemma essSup_eq_iSup (hμ : ∀ a, μ {a} ≠ 0) (f : α → β) : essSup f μ = ⨆ i, f i := by
  rw [essSup, ae_eq_top.2 hμ, limsup_top]

lemma essInf_eq_iInf (hμ : ∀ a, μ {a} ≠ 0) (f : α → β) : essInf f μ = ⨅ i, f i := by
  rw [essInf, ae_eq_top.2 hμ, liminf_top]
