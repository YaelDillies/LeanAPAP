import Mathlib.Algebra.GroupPower.Basic
import Mathlib.GroupTheory.GroupAction.Defs

section Pow
variable {α β : Type*} [Pow α β]

-- TODO: Replace `pow_ite`
@[to_additive existing (attr := simp) ite_smul]
lemma pow_ite' (P : Prop) [Decidable P] (a : α) (b c : β) :
    a ^ (if P then b else c) = if P then a ^ b else a ^ c := by split_ifs <;> rfl

-- TODO: Replace `ite_pow`
@[to_additive existing (attr := simp) smul_ite]
lemma ite_pow' (P : Prop) [Decidable P] (a b : α) (c : β) :
    (if P then a else b) ^ c = if P then a ^ c else b ^ c := by split_ifs <;> rfl

end Pow
