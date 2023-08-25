import Mathbin.Algebra.GroupPower.Basic
import Mathbin.GroupTheory.GroupAction.Defs

#align_import mathlib.algebra.group_power.basic

section Pow

variable {α β : Type _} [Pow α β]

-- TODO: Replace `pow_ite`
@[simp, to_additive ite_smul]
theorem pow_ite' (P : Prop) [Decidable P] (a : α) (b c : β) :
    (a ^ if P then b else c) = if P then a ^ b else a ^ c := by split_ifs <;> rfl

-- TODO: Replace `ite_pow`
@[simp, to_additive smul_ite]
theorem ite_pow' (P : Prop) [Decidable P] (a b : α) (c : β) :
    (if P then a else b) ^ c = if P then a ^ c else b ^ c := by split_ifs <;> rfl

end Pow

