import Mathbin.Algebra.Hom.Equiv.Basic

#align_import mathlib.algebra.hom.equiv.basic

open Function

variable {α β γ δ : Type _} [MulOneClass α] [MulOneClass β] [MulOneClass γ] [MulOneClass δ]

@[simp, to_additive]
theorem MulEquiv.comp_symm (e : β ≃* α) : (e : β →* α).comp (e.symm : α →* β) = MonoidHom.id α := by
  ext <;>
    simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, MulEquiv.self_comp_symm, id.def,
      MonoidHom.id_apply]

-- cf https://discord.com/channels/@me/827209384811561031/1079538520353423380
@[to_additive]
theorem Function.Injective.comp_mulEquiv (f : α → β →* γ) (hf : Injective f) (e : δ ≃* β) :
    Injective fun a => (f a).comp (e : δ →* β) :=
  by
  refine'
    (left_inverse.injective fun i => _ : injective fun i : β →* γ => i.comp (e : δ →* β)).comp hf
  · exact fun i => i.comp (e.symm : β →* δ)
  · simp [MonoidHom.comp_assoc]

