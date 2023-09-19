import Mathlib.Algebra.Hom.Equiv.Basic

open Function

variable {α β γ δ : Type*} [MulOneClass α] [MulOneClass β] [MulOneClass γ] [MulOneClass δ]

@[to_additive (attr := simp)]
lemma MulEquiv.comp_symm (e : β ≃* α) : (e : β →* α).comp (e.symm : α →* β) = MonoidHom.id α := by
  ext
  simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, MulEquiv.self_comp_symm, id.def,
    MonoidHom.id_apply]

-- cf https://discord.com/channels/@me/827209384811561031/1079538520353423380
@[to_additive]
lemma Function.Injective.comp_mulEquiv (f : α → β →* γ) (hf : Injective f) (e : δ ≃* β) :
    Injective λ a ↦ (f a).comp (e : δ →* β) := by
  refine'
    (LeftInverse.injective λ i ↦ _ : Injective λ i : β →* γ ↦ i.comp (e : δ →* β)).comp hf
  · exact λ i ↦ i.comp (e.symm : β →* δ)
  · simp [MonoidHom.comp_assoc]
