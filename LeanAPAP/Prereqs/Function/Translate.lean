import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Data.ZMod.Basic

/-!
# Precomposition operators
-/

open Function Set
open scoped ComplexConjugate Pointwise

/-! ### Translation operator -/

section translate
variable {ι α β γ : Type*} [AddCommGroup α]

def translate (a : α) (f : α → β) : α → β := fun x ↦ f (x - a)

notation "τ " => translate

@[simp] lemma translate_apply (a : α) (f : α → β) (x : α) : τ a f x = f (x - a) := rfl
@[simp] lemma translate_zero (f : α → β) : τ 0 f = f := by ext; simp

lemma translate_translate (a b : α) (f : α → β) : τ a (τ b f) = τ (a + b) f := by
  ext; simp [sub_sub]

lemma translate_add (a b : α) (f : α → β) : τ (a + b) f = τ a (τ b f) := by ext; simp [sub_sub]

lemma translate_add' (a b : α) (f : α → β) : τ (a + b) f = τ b (τ a f) := by
  rw [add_comm, translate_add]

lemma translate_comm (a b : α) (f : α → β) : τ a (τ b f) = τ b (τ a f) := by
  rw [← translate_add, translate_add']

@[simp] lemma comp_translate (a : α) (f : α → β) (g : β → γ) : g ∘ τ a f = τ a (g ∘ f) := rfl

@[simp]
lemma translate_smul_right [SMul γ β] (a : α) (f : α → β) (c : γ) : τ a (c • f) = c • τ a f := rfl

section AddCommMonoid
variable [AddCommMonoid β]

@[simp] lemma translate_zero_right (a : α) : τ a (0 : α → β) = 0 := rfl

lemma translate_add_right (a : α) (f g : α → β) : τ a (f + g) = τ a f + τ a g := rfl

lemma translate_sum_right (a : α) (f : ι → α → β) (s : Finset ι) :
    τ a (∑ i in s, f i) = ∑ i in s, τ a (f i) := by ext; simp

lemma sum_translate [Fintype α] (a : α) (f : α → β) : ∑ b, τ a f b = ∑ b, f b :=
  Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl

end AddCommMonoid

section AddCommGroup
variable [AddCommGroup β]

lemma translate_sub_right (a : α) (f g : α → β) : τ a (f - g) = τ a f - τ a g := rfl
lemma translate_neg_right (a : α) (f : α → β) : τ a (-f) = -τ a f := rfl

@[simp] lemma support_translate (a : α) (f : α → β) : support (τ a f) = a +ᵥ support f := by
  ext; simp [mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add]

end AddCommGroup

variable [CommRing β]

lemma translate_prod_right (a : α) (f : ι → α → β) (s : Finset ι) :
    τ a (∏ i in s, f i) = ∏ i in s, τ a (f i) := by ext; simp

end translate

open Fintype

variable {α β G 𝕜 : Type*} [AddCommGroup G]

noncomputable def dilate (f : G → 𝕜) (n : ℕ) : G → 𝕜 :=
  fun a ↦ f ((n⁻¹ : ZMod (Nat.card G)).val • a)

variable [Star 𝕜] {f : G → 𝕜}

protected lemma IsSelfAdjoint.dilate (hf : IsSelfAdjoint f) (n : ℕ) : IsSelfAdjoint (dilate f n) :=
  Pi.isSelfAdjoint.2 fun _g ↦ hf.apply _
