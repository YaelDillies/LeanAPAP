import algebra.hom.equiv.basic

open function

variables {α β γ δ : Type*} [mul_one_class α] [mul_one_class β] [mul_one_class γ] [mul_one_class δ]

@[simp, to_additive]
lemma mul_equiv.comp_symm (e : β ≃* α) : (e : β →* α).comp (e.symm : α →* β) = monoid_hom.id α :=
by ext; simp only [monoid_hom.coe_comp, monoid_hom.coe_coe, mul_equiv.self_comp_symm, id.def,
    monoid_hom.id_apply]

-- cf https://discord.com/channels/@me/827209384811561031/1079538520353423380
@[to_additive]
lemma function.injective.comp_mul_equiv (f : α → β →* γ) (hf : injective f) (e : δ ≃* β) :
  injective (λ a, (f a).comp (e : δ →* β)) :=
begin
  refine (left_inverse.injective (λ i, _) : injective $ λ i : β →* γ, i.comp (e : δ →* β)).comp hf,
  { exact λ i, i.comp (e.symm : β →* δ) },
  { simp [monoid_hom.comp_assoc] }
end
