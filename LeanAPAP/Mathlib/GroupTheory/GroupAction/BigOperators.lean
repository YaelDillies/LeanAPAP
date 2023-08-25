import Mathbin.Algebra.Module.Basic
import Mathbin.GroupTheory.GroupAction.BigOperators
import Project.Mathlib.Algebra.BigOperators.Pi

#align_import mathlib.group_theory.group_action.big_operators

open Finset Fintype

open scoped BigOperators

namespace Fintype

variable {α β γ : Type _} [DecidableEq α] [Fintype α] [AddCommMonoid γ]

theorem sum_fintype_apply (f : β → γ) (s : Finset β) (a : α) :
    ∑ g in piFinset fun _ : α => s, f (g a) = s.card ^ (card α - 1) • ∑ b in s, f b := by
  classical
  rw [sum_comp]
  simp only [image_pi_finset_const, filter_pi_finset_const_card s, ite_smul, zero_smul, smul_sum,
    sum_ite_mem, inter_self]

end Fintype

