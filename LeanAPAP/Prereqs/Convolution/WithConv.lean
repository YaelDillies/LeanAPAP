import LeanAPAP.Prereqs.Convolution.Discrete.Basic

/-!
# The ring of functions under convolution

For a finite group `G`, we define a type synonym `with_conv G R` of the functions `G → R`. We endow
that type synonym with the ring structure given by pointwise addition and convolution as
multiplication.
-/

open Finset Function
open scoped ComplexConjugate NNReal Pointwise

variable {G H R : Type*}

/-!
### The ring of functions under convolution

In this section, for a finite group `G`, we define a type synonym `with_conv G R` of the functions
`G → R`. We endow that type synonym with the ring structure given by pointwise addition and
convolution as multiplication.
-/

/-- Type synonym for the functions `G → R` where multiplication is given by convolution. -/
def WithConv (G R : Type*) := G → R

/-- `to_conv` is the "identity" function from `G → R` to `with_conv G R`. -/
def toConv : (G → R) ≃ WithConv G R := Equiv.refl _

/-- `of_conv` is the "identity" function from `with_conv G R` to `G → R`. -/
def ofConv : WithConv G R ≃ (G → R) := Equiv.refl _

@[simp] lemma toConv_symm_eq : (toConv : (G → R) ≃ WithConv G R).symm = ofConv := rfl
@[simp] lemma ofConv_symm_eq : (ofConv : WithConv G R ≃ (G → R)).symm = toConv := rfl
@[simp] lemma toConv_ofConv (f : WithConv G R) : toConv (ofConv f) = f := rfl
@[simp] lemma ofConv_toConv (f : G → R) : ofConv (toConv f) = f := rfl
@[simp] lemma toConv_inj {f g : G → R} : toConv f = toConv g ↔ f = g := Iff.rfl
@[simp] lemma ofConv_inj {f g : WithConv G R} : ofConv f = ofConv g ↔ f = g := Iff.rfl
@[simp] lemma toConv_apply (f : G → R) (a : G) : toConv f a = f a := rfl
@[simp] lemma ofConv_apply (f : WithConv G R) (a : G) : ofConv f a = f a := rfl

instance [Nonempty R] : Nonempty (WithConv G R) := Pi.instNonempty

section SMul
variable [SMul H R]

instance : SMul H (WithConv G R) := Pi.instSMul

@[simp] lemma toConv_smul (c : H) (f : G → R) : toConv (c • f) = c • f := rfl
@[simp] lemma ofConv_smul (c : H) (f : WithConv G R) : ofConv (c • f) = c • ofConv f := rfl

end SMul

variable [Fintype G] [DecidableEq G] [AddCommGroup G]

section CommSemiring
variable [CommSemiring R]

instance instCommSemiring : CommSemiring (WithConv G R) :=
  { Pi.addCommMonoid with
    one := toConv (Pi.single 0 1 : G → R)
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

@[simp] lemma toConv_zero : toConv (0 : G → R) = 0 := rfl
@[simp] lemma ofConv_zero : (ofConv 0 : G → R) = 0 := rfl
@[simp] lemma toConv_add (f g : G → R) : toConv (f + g) = toConv f + toConv g := rfl
@[simp] lemma ofConv_add (f g : WithConv G R) : ofConv (f + g) = ofConv f + ofConv g := rfl
@[simp] lemma ofConv_mul (f g : WithConv G R) : ofConv (f * g) = ofConv f ∗ ofConv g := rfl
@[simp] lemma toConv_conv (f g : G → R) : toConv (f ∗ g) = toConv f * toConv g := rfl

end CommSemiring

section CommRing
variable [CommRing R]

instance : CommRing (WithConv G R) := { instCommSemiring, Pi.addCommGroup with }

@[simp] lemma toConv_neg (f : G → R) : toConv (-f) = -toConv f := rfl
@[simp] lemma ofConv_neg (f : WithConv G R) : ofConv (-f) = -ofConv f := rfl
@[simp] lemma toConv_sub (f g : G → R) : toConv (f - g) = toConv f - toConv g := rfl
@[simp] lemma ofConv_sub (f g : WithConv G R) : ofConv (f - g) = ofConv f - ofConv g := rfl

end CommRing
