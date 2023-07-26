import prereqs.convolution.basic

/-!
# The ring of functions under convolution

For a finite group `α`, we define a type synonym `with_conv α β` of the functions `α → β`. We endow
that type synonym with the ring structure given by pointwise addition and convolution as
multiplication.
-/

open finset function
open_locale big_operators complex_conjugate nnreal pointwise

variables {α β γ : Type*} [fintype α] [decidable_eq α] [add_comm_group α]

/-!
### The ring of functions under convolution

In this section, for a finite group `α`, we define a type synonym `with_conv α β` of the functions
`α → β`. We endow that type synonym with the ring structure given by pointwise addition and
convolution as multiplication.
-/

/-- Type synonym for the functions `α → β` where multiplication is given by convolution. -/
def with_conv (α β : Type*) : Type* := α → β

/-- `to_conv` is the "identity" function from `α → β` to `with_conv α β`. -/
@[nolint unused_arguments]
def to_conv : (α → β) ≃ with_conv α β := equiv.refl _

/-- `of_conv` is the "identity" function from `with_conv α β` to `α → β`. -/
@[nolint unused_arguments]
def of_conv : with_conv α β ≃ (α → β) := equiv.refl _

@[simp] lemma to_conv_symm_eq : (to_conv : (α → β) ≃ with_conv α β).symm = of_conv := rfl
@[simp] lemma of_conv_symm_eq : (of_conv : with_conv α β ≃ (α → β)).symm = to_conv := rfl
@[simp] lemma to_conv_of_conv (f : with_conv α β) : to_conv (of_conv f) = f := rfl
@[simp] lemma of_conv_to_conv (f : α → β) : of_conv (to_conv f) = f := rfl
@[simp] lemma to_conv_inj {f g : α → β} : to_conv f = to_conv g ↔ f = g := iff.rfl
@[simp] lemma of_conv_inj {f g : with_conv α β} : of_conv f = of_conv g ↔ f = g := iff.rfl

@[simp] lemma to_conv_apply (f : α → β) (a : α) : to_conv f a = f a := rfl
@[simp] lemma of_conv_apply (f : with_conv α β) (a : α) : of_conv f a = f a := rfl

@[nolint unused_arguments fintype_finite decidable_classical]
instance [nonempty β] : nonempty (with_conv α β) := pi.nonempty

section comm_semiring
variables [comm_semiring β] [star_ring β]

instance : comm_semiring (with_conv α β) :=
{ one := to_conv (pi.single 0 1 : α → β),
  mul := λ f g, to_conv $ of_conv f ∗ of_conv g,
  mul_assoc := conv_assoc,
  mul_comm := conv_comm,
  mul_zero := conv_zero,
  zero_mul := zero_conv,
  mul_one := λ f, funext $ λ a, by simp [conv_eq_sum_sub, pi.single_apply],
  one_mul := λ f, funext $ λ a, by simp [conv_eq_sum_sub', pi.single_apply],
  left_distrib := conv_add,
  right_distrib := add_conv,
  ..pi.add_comm_monoid }

@[nolint unused_arguments]
instance [has_smul γ β] : has_smul γ (with_conv α β) := pi.has_smul

@[simp] lemma to_conv_zero : to_conv (0 : α → β) = 0 := rfl
@[simp] lemma of_conv_zero : (of_conv 0 : α → β) = 0 := rfl
@[simp] lemma to_conv_add (f g : α → β) : to_conv (f + g) = to_conv f + to_conv g := rfl
@[simp] lemma of_conv_add (f g : with_conv α β) : of_conv (f + g) = of_conv f + of_conv g := rfl
@[simp] lemma to_conv_smul [has_smul γ β] (c : γ) (f : α → β) : to_conv (c • f) = c • f := rfl
@[simp] lemma of_conv_smul [has_smul γ β] (c : γ) (f : with_conv α β) :
  of_conv (c • f) = c • of_conv f := rfl

@[simp] lemma of_conv_mul (f g : with_conv α β) : of_conv (f * g) = of_conv f ∗ of_conv g := rfl
@[simp] lemma to_conv_conv (f g : α → β) : to_conv (f ∗ g) = to_conv f * to_conv g := rfl

end comm_semiring

section comm_ring
variables [comm_ring β] [star_ring β]

instance : comm_ring (with_conv α β) := { ..with_conv.comm_semiring, ..pi.add_comm_group }

@[simp] lemma to_conv_neg (f : α → β) : to_conv (-f) = -to_conv f := rfl
@[simp] lemma of_conv_neg (f : with_conv α β) : of_conv (-f) = -of_conv f := rfl
@[simp] lemma to_conv_sub (f g : α → β) : to_conv (f - g) = to_conv f - to_conv g := rfl
@[simp] lemma of_conv_sub (f g : with_conv α β) : of_conv (f - g) = of_conv f - of_conv g := rfl

end comm_ring
