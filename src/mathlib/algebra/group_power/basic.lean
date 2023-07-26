import algebra.group_power.basic
import group_theory.group_action.defs

section has_pow
variables {α β : Type*} [has_pow α β]

-- TODO: Replace `pow_ite`
@[simp, to_additive ite_smul] lemma pow_ite' (P : Prop) [decidable P] (a : α) (b c : β) :
  a ^ (if P then b else c) = if P then a ^ b else a ^ c :=
by split_ifs; refl

-- TODO: Replace `ite_pow`
@[simp, to_additive smul_ite] lemma ite_pow' (P : Prop) [decidable P] (a b : α) (c : β) :
  (if P then a else b) ^ c = if P then a ^ c else b ^ c :=
by split_ifs; refl

end has_pow
