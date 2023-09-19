import Mathlib.Algebra.Group.TypeTags

variable {α β : Type*}

namespace AddMonoidHom
variable [AddGroup α] [Group β]

--TODO: Add the other ones
@[simp, norm_cast]
lemma coe_toMultiplicative'' (f : α →+ Additive β) :
    ⇑(toMultiplicative'' f) = Additive.toMul ∘ f ∘ Multiplicative.toAdd := rfl

end AddMonoidHom

namespace Multiplicative

@[simp]
protected lemma «forall» {p : Multiplicative α → Prop} : (∀ a, p a) ↔ ∀ a, p (ofAdd a) := Iff.rfl

@[simp]
protected lemma «exists» {p : Multiplicative α → Prop} : (∃ a, p a) ↔ ∃ a, p (ofAdd a) := Iff.rfl

end Multiplicative

namespace Additive

@[simp]
protected lemma «forall» {p : Additive α → Prop} : (∀ a, p a) ↔ ∀ a, p (ofMul a) := Iff.rfl

@[simp]
protected lemma «exists» {p : Additive α → Prop} : (∃ a, p a) ↔ ∃ a, p (ofMul a) := Iff.rfl

end Additive
