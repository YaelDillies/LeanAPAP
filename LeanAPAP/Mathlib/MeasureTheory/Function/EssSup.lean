import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Measure.MeasureSpace
import LeanAPAP.Mathlib.Order.LiminfLimsup

open Filter MeasureTheory
open scoped ENNReal

variable {α β : Type*} {m : MeasurableSpace α} [ConditionallyCompleteLattice β]
  {μ : Measure α} {f : α → β}

section SMul
variable {R : Type*} [Zero R] [SMulWithZero R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
  [NoZeroSMulDivisors R ℝ≥0∞] {c : ℝ≥0∞}

-- TODO: Replace in mathlib
@[simp] lemma essSup_smul_measure' {f : α → β} {c : ℝ≥0∞} (hc : c ≠ 0) :
    essSup f (c • μ) = essSup f μ := by simp_rw [essSup, Measure.ae_smul_measure_eq hc]

end SMul

variable [Nonempty α]

lemma essSup_eq_ciSup (hμ : ∀ a, μ {a} ≠ 0) (hf : BddAbove (Set.range f)) :
    essSup f μ = ⨆ a, f a := by rw [essSup, ae_eq_top.2 hμ, limsup_top_eq_ciSup hf]

lemma essInf_eq_ciInf (hμ : ∀ a, μ {a} ≠ 0) (hf : BddBelow (Set.range f)) :
    essInf f μ = ⨅ a, f a := by rw [essInf, ae_eq_top.2 hμ, liminf_top_eq_ciInf hf]

@[simp] lemma essSup_count_eq_ciSup [MeasurableSingletonClass α] (hf : BddAbove (Set.range f)) :
    essSup f .count = ⨆ a, f a := essSup_eq_ciSup (by simp) hf

@[simp] lemma essInf_count_eq_ciInf [MeasurableSingletonClass α] (hf : BddBelow (Set.range f)) :
    essInf f .count = ⨅ a, f a := essInf_eq_ciInf (by simp) hf
