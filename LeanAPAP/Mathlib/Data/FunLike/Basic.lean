import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Subtype
import Mathlib.Tactic.Coe

namespace Subtype
variable {F α : Type*} {β : α → Type*} {p : F → Prop} [DFunLike F α β]

instance : DFunLike {f // p f} α β where
  coe f := f.1
  coe_injective' := DFunLike.coe_injective.comp coe_injective

@[simp] lemma coe_coe (f : {f // p f}) : ⇑f.1 = f := rfl
@[simp] lemma mk_coe (f : F) (hf : p f) : ⇑(⟨f, hf⟩ : {f // p f}) = f := rfl
@[simp] lemma coe_apply (f : {f // p f}) (a : α) : f.1 a = f a := rfl
@[simp] lemma mk_apply (f : F) (hf : p f) (a : α) : (⟨f, hf⟩ : {f // p f}) a = f a := rfl

end Subtype
