import data.complex.basic

/-!
# Convolution

## TODO

Multiplicativise. Probably ugly and not very useful.
Include convolution on `α → ℝ`. Generalise to star rings?
-/

open finset
open_locale big_operators complex_conjugate

/-!
### The ring of functions under convolution

In this section, for a finite group `α`, we define a type synonym `with_conv α` of the functions
`α → ℂ`. We endow that type synonym with the ring structure given by pointwise addition and
convolution as multiplication.
-/

variables (α : Type*)

@[derive add_comm_group] def with_conv : Type* := α → ℂ

variables {α}

/-- `to_conv` is the identity function to the `order_conv` of a linear order.  -/
def to_conv : (α → ℂ) ≃ with_conv α := equiv.refl _

/-- `of_conv` is the identity function from the `order_conv` of a linear order.  -/
def of_conv : with_conv α ≃ (α → ℂ) := equiv.refl _

@[simp] lemma to_conv_symm_eq : (@to_conv α).symm = of_conv := rfl
@[simp] lemma of_conv_symm_eq : (@of_conv α).symm = to_conv := rfl
@[simp] lemma to_conv_of_conv (f : with_conv α) : to_conv (of_conv f) = f := rfl
@[simp] lemma of_conv_to_conv (f : α → ℂ) : of_conv (to_conv f) = f := rfl
@[simp] lemma to_conv_inj {f g : α → ℂ} : to_conv f = to_conv g ↔ f = g := iff.rfl
@[simp] lemma of_conv_inj {f g : with_conv α} : of_conv f = of_conv g ↔ f = g := iff.rfl

@[simp] lemma to_conv_apply (f : α → ℂ) (a : α) : to_conv f a = f a := rfl
@[simp] lemma of_conv_apply (f : with_conv α) (a : α) : of_conv f a = f a := rfl

variables {α}

section add_group
variables [add_group α] [fintype α] [decidable_eq α]

instance : ring (with_conv α) :=
{ one := to_conv $ pi.single 0 1,
  mul := λ f g, to_conv $ λ a, ∑ x in univ.filter (λ x : α × α, x.1 + x.2 = a), f x.1 * g x.2,
  mul_assoc := sorry,
  one_mul := sorry,
  mul_one := sorry,
  left_distrib := sorry,
  right_distrib := sorry,
  ..with_conv.add_comm_group _ }

@[simp] lemma to_conv_zero : to_conv (0 : α → ℂ) = 0 := rfl
@[simp] lemma to_conv_neg (f : α → ℂ) : to_conv (-f) = -to_conv f := rfl
@[simp] lemma to_conv_add (f g : α → ℂ) : to_conv (f + g) = to_conv f + to_conv g := rfl
@[simp] lemma to_conv_sub (f g : α → ℂ) : to_conv (f - g) = to_conv f - to_conv g := rfl

@[simp] lemma of_conv_zero : (of_conv 0 : α → ℂ) = 0 := rfl
@[simp] lemma of_conv_neg (f : with_conv α) : of_conv (-f) = -of_conv f := rfl
@[simp] lemma of_conv_add (f g : with_conv α) : of_conv (f + g) = of_conv f + of_conv g := rfl
@[simp] lemma of_conv_sub (f g : with_conv α) : of_conv (f - g) = of_conv f - of_conv g := rfl

end add_group

section add_comm_group
variables [add_comm_group α] [fintype α] [decidable_eq α]

instance : comm_ring (with_conv α) :=
{ mul_comm := sorry,
  ..with_conv.ring }

end add_comm_group

/-!
### Convolution of functions

In this section, we define the convolution `f ∗ g` of functions `α → ℂ` and translate ring
properties of `with_conv α` to properties of `∗`.
-/

notation f ` ∗ `:70 g:70 := of_conv (to_conv f * to_conv g)

section add_group
variables [add_group α] [fintype α] [decidable_eq α]

@[simp] lemma of_conv_mul (f g : with_conv α) : of_conv (f * g) = of_conv f ∗ of_conv g := rfl

lemma conv_assoc (f g h : α → ℂ) : f ∗ g ∗ h = f ∗ (g ∗ h) := mul_assoc (to_conv f) _ _

@[simp] lemma conv_zero (f : α → ℂ) : f ∗ 0 = 0 := mul_zero (to_conv f)
@[simp] lemma zero_conv (f : α → ℂ) : 0 ∗ f = 0 := zero_mul (to_conv f)

@[simp] lemma conv_neg (f g : α → ℂ) : f ∗ (-g) = -(f ∗ g) := congr_arg of_conv (mul_neg _ _)
@[simp] lemma neg_conv (f g : α → ℂ) : (-f) ∗ g = -(f ∗ g) := congr_arg of_conv (neg_mul _ _)

lemma conv_add (f g h : α → ℂ) : f ∗ (g + h) = f ∗ g + f ∗ h := congr_arg of_conv (mul_add _ _ _)
lemma add_conv (f g h : α → ℂ) : (f + g) ∗ h = f ∗ h + g ∗ h := congr_arg of_conv (add_mul _ _ _)

lemma conv_sub (f g h : α → ℂ) : f ∗ (g - h) = f ∗ g - f ∗ h := congr_arg of_conv (mul_sub _ _ _)
lemma sub_conv (f g h : α → ℂ) : (f - g) ∗ h = f ∗ h - g ∗ h := congr_arg of_conv (sub_mul _ _ _)

lemma conv_def (f g : α → ℂ) (a : α) : (f ∗ g) a = ∑ t, f (a - t) * g t := sorry

lemma conv_apply_add (f g : α → ℂ) (a b : α) : (f ∗ g) (a + b) = ∑ t, f (a + t) * g (b - t) := sorry


end add_group

section add_comm_group
variables [add_comm_group α] [fintype α] [decidable_eq α]

lemma conv_comm (f g : α → ℂ) : f ∗ g = g ∗ f := mul_comm (to_conv f) _

lemma conv_def' (f g : α → ℂ) (a : α) : (f ∗ g) a = ∑ t, f t * g (a - t) := sorry

end add_comm_group

/-!
### Difference convolution of functions

In this section, we define the difference convolution `f ○ g` of functions `α → ℂ` and show how it
interacts with the usual convolution.
-/

section add_group
variables [add_group α] [fintype α] [decidable_eq α]

/-- Difference convolution -/
def dconv (f g : α → ℂ) : α → ℂ :=
λ a, ∑ x in univ.filter (λ x : α × α, x.1 - x.2 = a), f x.1 * conj (g x.2)

end add_group

infix ` ○ `:70 := dconv

section add_comm_group
variables [add_comm_group α] [fintype α] [decidable_eq α]

@[simp] lemma dconv_zero (f : α → ℂ) : f ○ 0 = 0 := sorry
@[simp] lemma zero_dconv (f : α → ℂ) : 0 ○ f = 0 := sorry

@[simp] lemma dconv_neg (f g : α → ℂ) : f ○ (-g) = -(f ○ g) := sorry
@[simp] lemma neg_dconv (f g : α → ℂ) : (-f) ○ g = -(f ○ g) := sorry

lemma dconv_add (f g h : α → ℂ) : f ○ (g + h) = f ○ g + f ○ h := sorry
lemma add_dconv (f g h : α → ℂ) : (f + g) ○ h = f ○ h + g ○ h := sorry

lemma dconv_sub (f g h : α → ℂ) : f ○ (g - h) = f ○ g - f ○ h := sorry
lemma sub_dconv (f g h : α → ℂ) : (f - g) ○ h = f ○ h - g ○ h := sorry

lemma dconv_apply_neg (f g : α → ℂ) (a : α) : (f ○ g) (-a) = conj ((g ○ f) a) := sorry
lemma dconv_apply_sub (f g : α → ℂ) (a b : α) :
  (f ○ g) (a - b) = ∑ t, f (a + t) * conj (g (b + t)) := sorry

lemma dconv_def (f g : α → ℂ) (a : α) : (f ○ g) a = ∑ t, f (a + t) * conj (g t) := sorry
lemma dconv_def' (f g : α → ℂ) (a : α) : (f ○ g) a = ∑ t, f t * conj (g (t - a)) := sorry

end add_comm_group
