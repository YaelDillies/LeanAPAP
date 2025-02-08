import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

namespace MeasureTheory
variable {α β : Type*} {_ : MeasurableSpace α} [TopologicalSpace β] [Countable α]
  [MeasurableSingletonClass α] {f : α → β}

-- TODO: Replace, make args implicit
@[nontriviality] alias StronglyMeasurable.of_subsingleton_cod := Subsingleton.stronglyMeasurable
@[nontriviality] alias StronglyMeasurable.of_subsingleton_dom := Subsingleton.stronglyMeasurable'

-- TODO: Replace `StronglyMeasurable.of_finite`
lemma StronglyMeasurable.of_discrete : StronglyMeasurable f := by
  cases isEmpty_or_nonempty α
  · exact .of_subsingleton_dom _
  obtain _ | ⟨⟨b⟩⟩ := isEmpty_or_nonempty β
  · exact .of_subsingleton_cod _
  obtain ⟨g, hg⟩ := exists_surjective_nat α
  -- TODO: Lean bug, see
  -- let rec k : ℕ → SimpleFunc α β
  --   | 0 => .const _ b
  --   | n + 1 => .piecewise {g n} (.singleton _) (.const _ <| f (g n)) (k n)
  sorry
