import algebra.order.pi
import data.zmod.basic
import mathlib.algebra.star.order
import mathlib.algebra.star.pi
import mathlib.algebra.star.self_adjoint

/-!
# Precomposition operators
-/

open function set
open_locale big_operators complex_conjugate pointwise

/-! ### Translation operator -/

section translate
variables {ι α β γ : Type*} [add_comm_group α]

def translate (a : α) (f : α → β) : α → β := λ x, f (x - a)

notation `τ ` := translate

@[simp] lemma translate_apply (a : α) (f : α → β) (x : α) : τ a f x = f (x - a) := rfl

@[simp] lemma translate_zero (f : α → β) : translate 0 f = f := by ext; simp

@[simp] lemma translate_translate (a b : α) (f : α → β) : τ a (τ b f) = τ (a + b) f :=
by ext; simp [sub_sub]

@[simp] lemma comp_translate (a : α) (f : α → β) (g : β → γ) : g ∘ τ a f = τ a (g ∘ f) := rfl

@[simp] lemma translate_smul_right [has_smul γ β] (a : α) (f : α → β) (c : γ) :
  τ a (c • f) = c • τ a f := rfl

section add_comm_group
variables [add_comm_group β]

@[simp] lemma translate_zero_right (a : α) : τ a (0 : α → β) = 0 := rfl
lemma translate_add_right (a : α) (f g : α → β) : τ a (f + g) = τ a f + τ a g := rfl
lemma translate_sub_right (a : α) (f g : α → β) : τ a (f - g) = τ a f - τ a g := rfl
lemma translate_neg_right (a : α) (f : α → β) : τ a (-f) = -τ a f := rfl
lemma translate_sum_right (a : α) (f : ι → α → β) (s : finset ι) :
  τ a (∑ i in s, f i) = ∑ i in s, τ a (f i) := by ext; simp

lemma sum_translate [fintype α] (a : α) (f : α → β) : ∑ b, τ a f b = ∑ b, f b :=
fintype.sum_equiv (equiv.sub_right _) _ _ $ λ _, rfl

@[simp] lemma support_translate (a : α) (f : α → β) : support (τ a f) = a +ᵥ support f :=
by ext; simp [mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add]

end add_comm_group

variable [comm_ring β]

lemma translate_prod_right (a : α) (f : ι → α → β) (s : finset ι) :
  τ a (∏ i in s, f i) = ∏ i in s, τ a (f i) := by ext; simp

end translate

/-! ### Conjugation negation operator -/

section conjneg
variables {ι α β γ : Type*} [add_group α]

section comm_semiring
variables [comm_semiring β] [star_ring β] {f g : α → β}

def conjneg (f : α → β) : α → β := conj (λ x, f (-x))

@[simp] lemma conjneg_apply (f : α → β) (x : α) : conjneg f x = conj (f (-x)) := rfl
@[simp] lemma conjneg_conjneg (f : α → β) : conjneg (conjneg f) = f := by ext; simp

lemma conjneg_injective : injective (conjneg : (α → β) → α → β) :=
involutive.injective conjneg_conjneg

@[simp] lemma conjneg_inj : conjneg f = conjneg g ↔ f = g := conjneg_injective.eq_iff
lemma conjneg_ne_conjneg : conjneg f ≠ conjneg g ↔ f ≠ g := conjneg_injective.ne_iff

@[simp] lemma conjneg_zero : conjneg (0 : α → β) = 0 := by ext; simp
@[simp] lemma conjneg_one : conjneg (1 : α → β) = 1 := by ext; simp
@[simp] lemma conjneg_add (f g : α → β) : conjneg (f + g) = conjneg f + conjneg g := by ext; simp
@[simp] lemma conjneg_sum (s : finset ι) (f : ι → α → β) :
  conjneg (∑ i in s, f i) = ∑ i in s, conjneg (f i) :=
by ext; simp only [map_sum, conjneg_apply, finset.sum_apply]
@[simp] lemma conjneg_prod (s : finset ι) (f : ι → α → β) :
  conjneg (∏ i in s, f i) = ∏ i in s, conjneg (f i) :=
by ext; simp only [map_prod, conjneg_apply, finset.prod_apply]

@[simp] lemma conjneg_eq_zero : conjneg f = 0 ↔ f = 0 :=
by rw [←conjneg_inj, conjneg_conjneg, conjneg_zero]

@[simp] lemma conjneg_eq_one : conjneg f = 1 ↔ f = 1 :=
by rw [←conjneg_inj, conjneg_conjneg, conjneg_one]

lemma conjneg_ne_zero : conjneg f ≠ 0 ↔ f ≠ 0 := conjneg_eq_zero.not
lemma conjneg_ne_one : conjneg f ≠ 1 ↔ f ≠ 1 := conjneg_eq_one.not

lemma sum_conjneg [fintype α] (f : α → β) : ∑ a, conjneg f a = ∑ a, conj (f a) :=
fintype.sum_equiv (equiv.neg _) _ _ $ λ _, rfl

@[simp] lemma support_conjneg (f : α → β) : support (conjneg f) = -support f :=
by ext; simp [star_ring_end_apply]

end comm_semiring

section comm_ring
variables [comm_ring β] [star_ring β]

@[simp] lemma conjneg_sub (f g : α → β) : conjneg (f - g) = conjneg f - conjneg g := by ext; simp
@[simp] lemma conjneg_neg (f : α → β) : conjneg (-f) = -conjneg f := by ext; simp

end comm_ring

section ordered_comm_semiring
variables [ordered_comm_semiring β] [star_ordered_ring β] {f : α → β}

@[simp] lemma conjneg_nonneg : 0 ≤ conjneg f ↔ 0 ≤ f :=
(equiv.neg _).forall_congr $ λ x, star_nonneg

@[simp] lemma conjneg_pos : 0 < conjneg f ↔ 0 < f :=
by simp_rw [lt_iff_le_and_ne, @ne_comm (α → β) 0, conjneg_nonneg, conjneg_ne_zero]

end ordered_comm_semiring

section ordered_comm_ring
variables [ordered_comm_ring β] [star_ordered_ring β] {f : α → β}

@[simp] lemma conjneg_nonpos : conjneg f ≤ 0 ↔ f ≤ 0 :=
by simp_rw [←neg_nonneg, ←conjneg_neg, conjneg_nonneg]

@[simp] lemma conjneg_neg' : conjneg f < 0 ↔ f < 0 :=
by simp_rw [←neg_pos, ←conjneg_neg, conjneg_pos]

end ordered_comm_ring
end conjneg

open fintype

variables {α β G 𝕜 : Type*} [add_comm_group G]

variable [fintype G]

def dilate (f : G → 𝕜) (n : ℕ) : G → 𝕜 := λ a, f ((n⁻¹ : zmod (card G)).val • a)

variables [has_star 𝕜] {f : G → 𝕜}

protected lemma is_self_adjoint.dilate (hf : is_self_adjoint f) (n : ℕ) :
  is_self_adjoint (dilate f n) :=
pi.is_self_adjoint.2 $ λ g, hf.apply _
