import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Probability.ConditionalProbability

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β : Type*} {m : MeasurableSpace α} [ConditionallyCompleteLattice β]
  {μ : Measure α} {f : α → β}

variable [Nonempty α] [MeasurableSingletonClass α]

@[simp] lemma essSup_cond_count_eq_ciSup [Finite α] (hf : BddAbove (Set.range f)) :
    essSup f .count[|.univ] = ⨆ a, f a := essSup_eq_ciSup (by simp [cond_apply, Set.finite_univ]) hf

@[simp] lemma essInf_cond_count_eq_ciInf [Finite α] (hf : BddBelow (Set.range f)) :
    essInf f .count[|.univ] = ⨅ a, f a := essInf_eq_ciInf (by simp [cond_apply, Set.finite_univ]) hf
