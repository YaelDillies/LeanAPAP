import Mathlib.GroupTheory.GroupAction.Defs

section
variable {α β : Type*}

/-- Note that the `IsScalarTower α β β` typeclass argument is usually satisfied by `Algebra α β`.
-/
@[to_additive]
lemma smul_div_assoc [DivInvMonoid β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β) :
    r • x / y = r • (x / y) := by simp [div_eq_mul_inv, smul_mul_assoc]

end
