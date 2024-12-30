import Mathlib.MeasureTheory.Function.LpSpace

namespace MeasureTheory.Memℒp
variable {α E : Type*} {m0 : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] {p q : ENNReal} {f : α → E}

lemma mono_exponent (hpq : p ≤ q) (hfq : Memℒp f q μ) : Memℒp f p μ :=
  hfq.memℒp_of_exponent_le_of_measure_support_ne_top (by simp) (measure_ne_top _ .univ) hpq
