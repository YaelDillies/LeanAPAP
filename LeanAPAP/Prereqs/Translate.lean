import Mathbin.Algebra.Order.Pi
import Mathbin.Data.Zmod.Basic
import Project.Mathlib.Algebra.Star.Order
import Project.Mathlib.Algebra.Star.Pi
import Project.Mathlib.Algebra.Star.SelfAdjoint

#align_import prereqs.translate

/-!
# Precomposition operators
-/


open Function Set

open scoped BigOperators ComplexConjugate Pointwise

/-! ### Translation operator -/


section translate

variable {ι α β γ : Type _} [AddCommGroup α]

def translate (a : α) (f : α → β) : α → β := fun x => f (x - a)

notation "τ " => translate

@[simp]
theorem translate_apply (a : α) (f : α → β) (x : α) : τ a f x = f (x - a) :=
  rfl

@[simp]
theorem translate_zero (f : α → β) : translate 0 f = f := by ext <;> simp

@[simp]
theorem translate_translate (a b : α) (f : α → β) : τ a (τ b f) = τ (a + b) f := by
  ext <;> simp [sub_sub]

@[simp]
theorem comp_translate (a : α) (f : α → β) (g : β → γ) : g ∘ τ a f = τ a (g ∘ f) :=
  rfl

@[simp]
theorem translate_smul_right [SMul γ β] (a : α) (f : α → β) (c : γ) : τ a (c • f) = c • τ a f :=
  rfl

section AddCommGroup

variable [AddCommGroup β]

@[simp]
theorem translate_zero_right (a : α) : τ a (0 : α → β) = 0 :=
  rfl

theorem translate_add_right (a : α) (f g : α → β) : τ a (f + g) = τ a f + τ a g :=
  rfl

theorem translate_sub_right (a : α) (f g : α → β) : τ a (f - g) = τ a f - τ a g :=
  rfl

theorem translate_neg_right (a : α) (f : α → β) : τ a (-f) = -τ a f :=
  rfl

theorem translate_sum_right (a : α) (f : ι → α → β) (s : Finset ι) :
    τ a (∑ i in s, f i) = ∑ i in s, τ a (f i) := by ext <;> simp

theorem sum_translate [Fintype α] (a : α) (f : α → β) : ∑ b, τ a f b = ∑ b, f b :=
  Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ => rfl

@[simp]
theorem support_translate (a : α) (f : α → β) : support (τ a f) = a +ᵥ support f := by
  ext <;> simp [mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add]

end AddCommGroup

variable [CommRing β]

theorem translate_prod_right (a : α) (f : ι → α → β) (s : Finset ι) :
    τ a (∏ i in s, f i) = ∏ i in s, τ a (f i) := by ext <;> simp

end translate

/-! ### Conjugation negation operator -/


section conjneg

variable {ι α β γ : Type _} [AddGroup α]

section CommSemiring

variable [CommSemiring β] [StarRing β] {f g : α → β}

def conjneg (f : α → β) : α → β :=
  conj fun x => f (-x)

@[simp]
theorem conjneg_apply (f : α → β) (x : α) : conjneg f x = conj (f (-x)) :=
  rfl

@[simp]
theorem conjneg_conjneg (f : α → β) : conjneg (conjneg f) = f := by ext <;> simp

theorem conjneg_injective : Injective (conjneg : (α → β) → α → β) :=
  Involutive.injective conjneg_conjneg

@[simp]
theorem conjneg_inj : conjneg f = conjneg g ↔ f = g :=
  conjneg_injective.eq_iff

theorem conjneg_ne_conjneg : conjneg f ≠ conjneg g ↔ f ≠ g :=
  conjneg_injective.ne_iff

@[simp]
theorem conjneg_zero : conjneg (0 : α → β) = 0 := by ext <;> simp

@[simp]
theorem conjneg_one : conjneg (1 : α → β) = 1 := by ext <;> simp

@[simp]
theorem conjneg_add (f g : α → β) : conjneg (f + g) = conjneg f + conjneg g := by ext <;> simp

@[simp]
theorem conjneg_sum (s : Finset ι) (f : ι → α → β) :
    conjneg (∑ i in s, f i) = ∑ i in s, conjneg (f i) := by
  ext <;> simp only [map_sum, conjneg_apply, Finset.sum_apply]

@[simp]
theorem conjneg_prod (s : Finset ι) (f : ι → α → β) :
    conjneg (∏ i in s, f i) = ∏ i in s, conjneg (f i) := by
  ext <;> simp only [map_prod, conjneg_apply, Finset.prod_apply]

@[simp]
theorem conjneg_eq_zero : conjneg f = 0 ↔ f = 0 := by
  rw [← conjneg_inj, conjneg_conjneg, conjneg_zero]

@[simp]
theorem conjneg_eq_one : conjneg f = 1 ↔ f = 1 := by
  rw [← conjneg_inj, conjneg_conjneg, conjneg_one]

theorem conjneg_ne_zero : conjneg f ≠ 0 ↔ f ≠ 0 :=
  conjneg_eq_zero.Not

theorem conjneg_ne_one : conjneg f ≠ 1 ↔ f ≠ 1 :=
  conjneg_eq_one.Not

theorem sum_conjneg [Fintype α] (f : α → β) : ∑ a, conjneg f a = ∑ a, conj (f a) :=
  Fintype.sum_equiv (Equiv.neg _) _ _ fun _ => rfl

@[simp]
theorem support_conjneg (f : α → β) : support (conjneg f) = -support f := by
  ext <;> simp [starRingEnd_apply]

end CommSemiring

section CommRing

variable [CommRing β] [StarRing β]

@[simp]
theorem conjneg_sub (f g : α → β) : conjneg (f - g) = conjneg f - conjneg g := by ext <;> simp

@[simp]
theorem conjneg_neg (f : α → β) : conjneg (-f) = -conjneg f := by ext <;> simp

end CommRing

section OrderedCommSemiring

variable [OrderedCommSemiring β] [StarOrderedRing β] {f : α → β}

@[simp]
theorem conjneg_nonneg : 0 ≤ conjneg f ↔ 0 ≤ f :=
  (Equiv.neg _).forall_congr' fun x => star_nonneg

@[simp]
theorem conjneg_pos : 0 < conjneg f ↔ 0 < f := by
  simp_rw [lt_iff_le_and_ne, @ne_comm (α → β) 0, conjneg_nonneg, conjneg_ne_zero]

end OrderedCommSemiring

section OrderedCommRing

variable [OrderedCommRing β] [StarOrderedRing β] {f : α → β}

@[simp]
theorem conjneg_nonpos : conjneg f ≤ 0 ↔ f ≤ 0 := by
  simp_rw [← neg_nonneg, ← conjneg_neg, conjneg_nonneg]

@[simp]
theorem conjneg_neg' : conjneg f < 0 ↔ f < 0 := by simp_rw [← neg_pos, ← conjneg_neg, conjneg_pos]

end OrderedCommRing

end conjneg

open Fintype

variable {α β G 𝕜 : Type _} [AddCommGroup G]

variable [Fintype G]

def dilate (f : G → 𝕜) (n : ℕ) : G → 𝕜 := fun a => f ((n⁻¹ : ZMod (card G)).val • a)

variable [Star 𝕜] {f : G → 𝕜}

protected theorem IsSelfAdjoint.dilate (hf : IsSelfAdjoint f) (n : ℕ) :
    IsSelfAdjoint (dilate f n) :=
  Pi.isSelfAdjoint.2 fun g => hf.apply _

