import Mathlib.Algebra.Group.Action.Defs

@[to_additive]
lemma smul_mul_smul_comm {α β : Type*} [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β]
    [IsScalarTower α α β] [SMulCommClass β α β] (a : α) (b : β) (c : α) (d : β) :
    (a • b) * c • d = (a * c) • (b * d) := smul_smul_smul_comm a b c d
