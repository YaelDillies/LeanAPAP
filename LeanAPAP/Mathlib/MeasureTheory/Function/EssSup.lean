import LeanAPAP.Mathlib.Order.LiminfLimsup
import Mathlib.MeasureTheory.Function.EssSup

open Filter MeasureTheory

variable {α β : Type*} [Nonempty α] {m : MeasurableSpace α} [ConditionallyCompleteLattice β]
  {μ : Measure α} {f : α → β}

lemma essSup_eq_ciSup (hμ : ∀ a, μ {a} ≠ 0) (hf : BddAbove (Set.range f)) :
    essSup f μ = ⨆ a, f a := by rw [essSup, ae_eq_top.2 hμ, limsup_top_eq_ciSup hf]

lemma essInf_eq_ciInf (hμ : ∀ a, μ {a} ≠ 0) (hf : BddBelow (Set.range f)) :
    essInf f μ = ⨅ a, f a := by rw [essInf, ae_eq_top.2 hμ, liminf_top_eq_ciInf hf]

@[simp] lemma essSup_count_eq_ciSup [MeasurableSingletonClass α] (hf : BddAbove (Set.range f)) :
    essSup f .count = ⨆ a, f a := essSup_eq_ciSup (by simp) hf

@[simp] lemma essInf_count_eq_ciInf [MeasurableSingletonClass α] (hf : BddBelow (Set.range f)) :
    essInf f .count = ⨅ a, f a := essInf_eq_ciInf (by simp) hf
