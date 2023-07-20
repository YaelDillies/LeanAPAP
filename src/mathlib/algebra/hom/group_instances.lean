import algebra.hom.group_instances

variables {α β : Type*} [mul_one_class α] [comm_monoid β]

@[simp, to_additive] lemma monoid_hom.pow_apply (n : ℕ) (f : α →* β) (x : α) :
  (f ^ n) x = f x ^ n := rfl
