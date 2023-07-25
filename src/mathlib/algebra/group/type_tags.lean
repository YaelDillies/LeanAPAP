import algebra.group.type_tags

variables {α β : Type*}

section
variables [add_group α] [group β]

--TODO: Add the other ones
@[simp, norm_cast] lemma add_monoid_hom.coe_to_multiplicative'' (f : α →+ additive β) :
  ⇑f.to_multiplicative'' = additive.to_mul ∘ f ∘ multiplicative.to_add := rfl

end

namespace multiplicative

@[simp] protected lemma «forall» {p : multiplicative α → Prop} : (∀ a, p a) ↔ ∀ a, p (of_add a) :=
iff.rfl

@[simp] protected lemma «exists» {p : multiplicative α → Prop} : (∃ a, p a) ↔ ∃ a, p (of_add a) :=
iff.rfl

end multiplicative

namespace additive

@[simp] protected lemma «forall» {p : additive α → Prop} : (∀ a, p a) ↔ ∀ a, p (of_mul a) := iff.rfl
@[simp] protected lemma «exists» {p : additive α → Prop} : (∃ a, p a) ↔ ∃ a, p (of_mul a) := iff.rfl

end additive
