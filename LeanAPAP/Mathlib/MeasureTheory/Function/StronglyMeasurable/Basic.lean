import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

open Filter Function

namespace MeasureTheory
variable {α β : Type*} {_ : MeasurableSpace α} [MeasurableSingletonClass α]
  {f : α → β} {b : β} {g : ℕ → α} {m : ℕ}

-- TODO: Replace, make args implicit
@[nontriviality] alias StronglyMeasurable.of_subsingleton_cod := Subsingleton.stronglyMeasurable
@[nontriviality] alias StronglyMeasurable.of_subsingleton_dom := Subsingleton.stronglyMeasurable'

/-- Auxiliary definition for `StronglyMeasurable.of_discrete`. -/
private noncomputable def simpleFuncAux (f : α → β) (b : β) (g : ℕ → α) : ℕ → SimpleFunc α β
  | 0 => .const _ b
  | n + 1 => .piecewise {g n} (.singleton _) (.const _ <| f (g n)) (simpleFuncAux f b g n)

private lemma simpleFuncAux_eq_of_lt :
    ∀ n > m, simpleFuncAux f b g n (g m) = f (g m)
  | _, .refl => by simp [simpleFuncAux]
  | _, Nat.le.step (m := n) hmn => by
    obtain hnm | hnm := eq_or_ne (g n) (g m) <;>
      simp [simpleFuncAux, Set.piecewise_eq_of_not_mem , hnm.symm, simpleFuncAux_eq_of_lt _ hmn]

private lemma simpleFuncAux_eventuallyEq :
    ∀ᶠ n in atTop, simpleFuncAux f b g n (g m) = f (g m) :=
  eventually_atTop.2 ⟨_, simpleFuncAux_eq_of_lt⟩

-- TODO: Replace `StronglyMeasurable.of_finite`
lemma StronglyMeasurable.of_discrete [TopologicalSpace β] [Countable α] : StronglyMeasurable f := by
  cases isEmpty_or_nonempty α
  · exact .of_subsingleton_dom _
  obtain _ | ⟨⟨b⟩⟩ := isEmpty_or_nonempty β
  · exact .of_subsingleton_cod _
  obtain ⟨g, hg⟩ := exists_surjective_nat α
  exact ⟨simpleFuncAux f b g, hg.forall.2 fun m ↦
    tendsto_nhds_of_eventually_eq simpleFuncAux_eventuallyEq⟩

end MeasureTheory
