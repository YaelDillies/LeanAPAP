import Mathlib.Algebra.Group.AddChar

variable {G R : Type*}

namespace AddChar
variable [AddMonoid G] [CommMonoid R] {ψ : AddChar G R}

@[simp] lemma toMonoidHomEquiv_zero : toMonoidHomEquiv (0 : AddChar G R) = 1 := rfl
@[simp] lemma toMonoidHomEquiv_symm_one :
    toMonoidHomEquiv.symm (1 : Multiplicative G →* R) = 0 := rfl

@[simp] lemma toMonoidHomEquiv_add (ψ φ : AddChar G R) :
    toMonoidHomEquiv (ψ + φ) = toMonoidHomEquiv ψ * toMonoidHomEquiv φ := rfl
@[simp] lemma toMonoidHomEquiv_symm_mul (ψ φ : Multiplicative G →* R) :
  toMonoidHomEquiv.symm (ψ * φ) = toMonoidHomEquiv.symm ψ + toMonoidHomEquiv.symm φ := rfl

@[simp, norm_cast] lemma coe_eq_one : ⇑ψ = 1 ↔ ψ = 0 := by rw [← coe_zero, DFunLike.coe_fn_eq]

noncomputable instance : DecidableEq (AddChar G R) := Classical.decEq _

end AddChar
