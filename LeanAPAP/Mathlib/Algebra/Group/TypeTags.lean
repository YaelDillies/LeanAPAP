import Mathlib.Algebra.Group.TypeTags

#align_import mathlib.algebra.group.type_tags

variable {α β : Type*}

section

variable [AddGroup α] [Group β]

--TODO: Add the other ones
@[simp, norm_cast]
lemma AddMonoidHom.coe_toMultiplicative'' (f : α →+ Additive β) :
    ⇑f.toMultiplicative'' = Additive.toMul ∘ f ∘ Multiplicative.toAdd := rfl

end

namespace Multiplicative

@[simp]
protected lemma forall {p : Multiplicative α → Prop} : (∀ a, p a) ↔ ∀ a, p (ofAdd a) :=
  Iff.rfl

@[simp]
protected lemma exists {p : Multiplicative α → Prop} : (∃ a, p a) ↔ ∃ a, p (ofAdd a) :=
  Iff.rfl

end Multiplicative

namespace Additive

@[simp]
protected lemma forall {p : Additive α → Prop} : (∀ a, p a) ↔ ∀ a, p (ofMul a) :=
  Iff.rfl

@[simp]
protected lemma exists {p : Additive α → Prop} : (∃ a, p a) ↔ ∃ a, p (ofMul a) :=
  Iff.rfl

end Additive
