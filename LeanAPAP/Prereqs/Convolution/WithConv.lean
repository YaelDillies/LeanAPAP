import Project.Prereqs.Convolution.Basic

#align_import prereqs.convolution.with_conv

/-!
# The ring of functions under convolution

For a finite group `α`, we define a type synonym `with_conv α β` of the functions `α → β`. We endow
that type synonym with the ring structure given by pointwise addition and convolution as
multiplication.
-/


open Finset Function

open scoped BigOperators ComplexConjugate NNReal Pointwise

variable {α β γ : Type _} [Fintype α] [DecidableEq α] [AddCommGroup α]

/-!
### The ring of functions under convolution

In this section, for a finite group `α`, we define a type synonym `with_conv α β` of the functions
`α → β`. We endow that type synonym with the ring structure given by pointwise addition and
convolution as multiplication.
-/


/-- Type synonym for the functions `α → β` where multiplication is given by convolution. -/
def WithConv (α β : Type _) : Type _ :=
  α → β

/-- `to_conv` is the "identity" function from `α → β` to `with_conv α β`. -/
@[nolint unused_arguments]
def toConv : (α → β) ≃ WithConv α β :=
  Equiv.refl _

/-- `of_conv` is the "identity" function from `with_conv α β` to `α → β`. -/
@[nolint unused_arguments]
def ofConv : WithConv α β ≃ (α → β) :=
  Equiv.refl _

@[simp]
theorem toConv_symm_eq : (toConv : (α → β) ≃ WithConv α β).symm = ofConv :=
  rfl

@[simp]
theorem ofConv_symm_eq : (ofConv : WithConv α β ≃ (α → β)).symm = toConv :=
  rfl

@[simp]
theorem toConv_ofConv (f : WithConv α β) : toConv (ofConv f) = f :=
  rfl

@[simp]
theorem ofConv_toConv (f : α → β) : ofConv (toConv f) = f :=
  rfl

@[simp]
theorem toConv_inj {f g : α → β} : toConv f = toConv g ↔ f = g :=
  Iff.rfl

@[simp]
theorem ofConv_inj {f g : WithConv α β} : ofConv f = ofConv g ↔ f = g :=
  Iff.rfl

@[simp]
theorem toConv_apply (f : α → β) (a : α) : toConv f a = f a :=
  rfl

@[simp]
theorem ofConv_apply (f : WithConv α β) (a : α) : ofConv f a = f a :=
  rfl

@[nolint unused_arguments fintype_finite decidable_classical]
instance [Nonempty β] : Nonempty (WithConv α β) :=
  Pi.nonempty

section CommSemiring

variable [CommSemiring β] [StarRing β]

instance : CommSemiring (WithConv α β) :=
  { Pi.addCommMonoid with
    one := toConv (Pi.single 0 1 : α → β)
    mul := fun f g => toConv <| ofConv f ∗ ofConv g
    mul_assoc := conv_assoc
    mul_comm := conv_comm
    mul_zero := conv_zero
    zero_mul := zero_conv
    mul_one := fun f => funext fun a => by simp [conv_eq_sum_sub, Pi.single_apply]
    one_mul := fun f => funext fun a => by simp [conv_eq_sum_sub', Pi.single_apply]
    left_distrib := conv_add
    right_distrib := add_conv }

@[nolint unused_arguments]
instance [SMul γ β] : SMul γ (WithConv α β) :=
  Pi.instSMul

@[simp]
theorem toConv_zero : toConv (0 : α → β) = 0 :=
  rfl

@[simp]
theorem ofConv_zero : (ofConv 0 : α → β) = 0 :=
  rfl

@[simp]
theorem toConv_add (f g : α → β) : toConv (f + g) = toConv f + toConv g :=
  rfl

@[simp]
theorem ofConv_add (f g : WithConv α β) : ofConv (f + g) = ofConv f + ofConv g :=
  rfl

@[simp]
theorem toConv_smul [SMul γ β] (c : γ) (f : α → β) : toConv (c • f) = c • f :=
  rfl

@[simp]
theorem ofConv_smul [SMul γ β] (c : γ) (f : WithConv α β) : ofConv (c • f) = c • ofConv f :=
  rfl

@[simp]
theorem ofConv_hMul (f g : WithConv α β) : ofConv (f * g) = ofConv f ∗ ofConv g :=
  rfl

@[simp]
theorem toConv_conv (f g : α → β) : toConv (f ∗ g) = toConv f * toConv g :=
  rfl

end CommSemiring

section CommRing

variable [CommRing β] [StarRing β]

instance : CommRing (WithConv α β) :=
  { WithConv.commSemiring, Pi.addCommGroup with }

@[simp]
theorem toConv_neg (f : α → β) : toConv (-f) = -toConv f :=
  rfl

@[simp]
theorem ofConv_neg (f : WithConv α β) : ofConv (-f) = -ofConv f :=
  rfl

@[simp]
theorem toConv_sub (f g : α → β) : toConv (f - g) = toConv f - toConv g :=
  rfl

@[simp]
theorem ofConv_sub (f g : WithConv α β) : ofConv (f - g) = ofConv f - ofConv g :=
  rfl

end CommRing

