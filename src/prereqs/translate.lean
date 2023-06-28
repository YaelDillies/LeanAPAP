import algebra.big_operators.pi
import mathlib.algebra.star.pi

/-!
# Precomposition operators
-/

open set
open_locale big_operators complex_conjugate

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

end add_comm_group

variable [comm_ring β]

lemma translate_prod_right (a : α) (f : ι → α → β) (s : finset ι) :
  τ a (∏ i in s, f i) = ∏ i in s, τ a (f i) := by ext; simp

end translate

/-! ### Conjugation negation operator -/

section conjneg
variables {ι α β γ : Type*} [fintype ι] [add_comm_group α]

section comm_semiring
variables [comm_semiring β] [star_ring β]

def conjneg (f : α → β) : α → β := conj (λ x, f (-x))

@[simp] lemma conjneg_apply (f : α → β) (x : α) : conjneg f x = conj (f (-x)) := rfl
@[simp] lemma conjneg_conjneg (f : α → β) : conjneg (conjneg f) = f := by ext; simp
@[simp] lemma conjneg_zero : conjneg (0 : α → β) = 0 := by ext; simp
@[simp] lemma conjneg_add (f g : α → β) : conjneg (f + g) = conjneg f + conjneg g := by ext; simp
@[simp] lemma conjneg_sum (f : ι → α → β) : conjneg (∑ i, f i) = ∑ i, conjneg (f i) :=
by ext; simp only [map_sum, conjneg_apply, fintype.sum_apply]
@[simp] lemma conjneg_prod (f : ι → α → β) : conjneg (∏ i, f i) = ∏ i, conjneg (f i) :=
by ext; simp only [map_prod, conjneg_apply, fintype.prod_apply]

end comm_semiring

section comm_ring
variables [comm_ring β] [star_ring β]

@[simp] lemma conjneg_sub (f g : α → β) : conjneg (f - g) = conjneg f - conjneg g := by ext; simp
@[simp] lemma conjneg_neg (f : α → β) : conjneg (-f) = -conjneg f := by ext; simp

end comm_ring
end conjneg
