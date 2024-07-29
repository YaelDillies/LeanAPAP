import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import LeanAPAP.Prereqs.EssSupCount

open TopologicalSpace MeasureTheory Filter
open scoped NNReal ENNReal Topology

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]

lemma snormEssSup_eq_iSup (hμ : ∀ a, μ {a} ≠ 0) (f : α → E) : snormEssSup f μ = ⨆ a, ↑‖f a‖₊ :=
  essSup_eq_iSup hμ _

@[simp] lemma snormEssSup_count [MeasurableSingletonClass α] (f : α → E) :
    snormEssSup f .count = ⨆ a, ↑‖f a‖₊ := essSup_count _
