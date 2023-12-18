import LeanAPAP.Prereqs.Discrete.Convolution.Basic

/-!
# The ring of functions under convolution

For a finite group `α`, we define a type synonym `with_conv α β` of the functions `α → β`. We endow
that type synonym with the ring structure given by pointwise addition and convolution as
multiplication.
-/

open Finset Function

open scoped BigOperators ComplexConjugate NNReal Pointwise

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [AddCommGroup α]

/-!
### The ring of functions under convolution

In this section, for a finite group `α`, we define a type synonym `with_conv α β` of the functions
`α → β`. We endow that type synonym with the ring structure given by pointwise addition and
convolution as multiplication.
-/

/-- Type synonym for the functions `α → β` where multiplication is given by convolution. -/
def WithConv (α β : Type*) := α → β

/-- `to_conv` is the "identity" function from `α → β` to `with_conv α β`. -/
def toConv : (α → β) ≃ WithConv α β := Equiv.refl _

/-- `of_conv` is the "identity" function from `with_conv α β` to `α → β`. -/
def ofConv : WithConv α β ≃ (α → β) := Equiv.refl _

@[simp] lemma toConv_symm_eq : (toConv : (α → β) ≃ WithConv α β).symm = ofConv := rfl
@[simp] lemma ofConv_symm_eq : (ofConv : WithConv α β ≃ (α → β)).symm = toConv := rfl
@[simp] lemma toConv_ofConv (f : WithConv α β) : toConv (ofConv f) = f := rfl
@[simp] lemma ofConv_toConv (f : α → β) : ofConv (toConv f) = f := rfl
@[simp] lemma toConv_inj {f g : α → β} : toConv f = toConv g ↔ f = g := Iff.rfl
@[simp] lemma ofConv_inj {f g : WithConv α β} : ofConv f = ofConv g ↔ f = g := Iff.rfl
@[simp] lemma toConv_apply (f : α → β) (a : α) : toConv f a = f a := rfl
@[simp] lemma ofConv_apply (f : WithConv α β) (a : α) : ofConv f a = f a := rfl

instance [Nonempty β] : Nonempty (WithConv α β) := Pi.Nonempty

section CommSemiring
variable [CommSemiring β] [StarRing β]

instance instCommSemiring : CommSemiring (WithConv α β) :=
  { Pi.addCommMonoid with
    one := toConv (Pi.single 0 1 : α → β)
    mul := fun f g ↦ toConv $ ofConv f ∗ ofConv g
    mul_assoc := conv_assoc
    mul_comm := conv_comm
    mul_zero := conv_zero
    zero_mul := zero_conv
    mul_one := fun f ↦ funext fun a ↦ show (ofConv f ∗ Pi.single 0 1) a = _ by
      simp [conv_eq_sum_sub, Pi.single_apply]
    one_mul := fun f ↦ funext fun a ↦ show (Pi.single 0 1 ∗ ofConv f) a = _ by
      simp [conv_eq_sum_sub', Pi.single_apply]
    left_distrib := conv_add
    right_distrib := add_conv }

instance [SMul γ β] : SMul γ (WithConv α β) := Pi.instSMul

@[simp] lemma toConv_zero : toConv (0 : α → β) = 0 := rfl
@[simp] lemma ofConv_zero : (ofConv 0 : α → β) = 0 := rfl
@[simp] lemma toConv_add (f g : α → β) : toConv (f + g) = toConv f + toConv g := rfl
@[simp] lemma ofConv_add (f g : WithConv α β) : ofConv (f + g) = ofConv f + ofConv g := rfl
@[simp] lemma toConv_smul [SMul γ β] (c : γ) (f : α → β) : toConv (c • f) = c • f := rfl
@[simp] lemma ofConv_smul [SMul γ β] (c : γ) (f : WithConv α β) : ofConv (c • f) = c • ofConv f :=
  rfl
@[simp] lemma ofConv_mul (f g : WithConv α β) : ofConv (f * g) = ofConv f ∗ ofConv g := rfl
@[simp] lemma toConv_conv (f g : α → β) : toConv (f ∗ g) = toConv f * toConv g := rfl

end CommSemiring

section CommRing
variable [CommRing β] [StarRing β]

instance : CommRing (WithConv α β) := { instCommSemiring, Pi.addCommGroup with }

@[simp] lemma toConv_neg (f : α → β) : toConv (-f) = -toConv f := rfl
@[simp] lemma ofConv_neg (f : WithConv α β) : ofConv (-f) = -ofConv f := rfl
@[simp] lemma toConv_sub (f g : α → β) : toConv (f - g) = toConv f - toConv g := rfl
@[simp] lemma ofConv_sub (f g : WithConv α β) : ofConv (f - g) = ofConv f - ofConv g := rfl

end CommRing
