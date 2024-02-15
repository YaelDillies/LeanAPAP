import Mathlib.Algebra.Module.Basic
import Mathlib.GroupTheory.GroupAction.BigOperators
import LeanAPAP.Mathlib.Algebra.BigOperators.Pi

open Finset Fintype
open scoped BigOperators

namespace Fintype
variable {α β γ : Type*} [DecidableEq α] [Fintype α] [AddCommMonoid γ]

lemma sum_piFinset_apply (f : β → γ) (s : Finset β) (a : α) :
    ∑ g in piFinset fun _ : α ↦ s, f (g a) = s.card ^ (card α - 1) • ∑ b in s, f b := by
  classical
  rw [sum_comp]
  simp only [image_piFinset_const, filter_piFinset_const_card s, ite_smul, zero_smul, smul_sum,
    sum_ite_mem, inter_self]

end Fintype
