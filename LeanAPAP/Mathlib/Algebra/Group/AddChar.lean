import Mathlib.Algebra.Group.AddChar

/-!
# TODO

Unsimp `AddChar.sub_apply`
-/

variable {A M : Type*}

namespace AddChar
section
variable [AddMonoid A] [CommMonoid M] {ψ : AddChar A M}

@[simp] lemma toMonoidHomEquiv_zero : toMonoidHomEquiv (0 : AddChar A M) = 1 := rfl
@[simp] lemma toMonoidHomEquiv_symm_one :
    toMonoidHomEquiv.symm (1 : Multiplicative A →* M) = 0 := rfl

@[simp] lemma toMonoidHomEquiv_add (ψ φ : AddChar A M) :
    toMonoidHomEquiv (ψ + φ) = toMonoidHomEquiv ψ * toMonoidHomEquiv φ := rfl
@[simp] lemma toMonoidHomEquiv_symm_mul (ψ φ : Multiplicative A →* M) :
  toMonoidHomEquiv.symm (ψ * φ) = toMonoidHomEquiv.symm ψ + toMonoidHomEquiv.symm φ := rfl

@[simp, norm_cast] lemma coe_eq_one : ⇑ψ = 1 ↔ ψ = 0 := by rw [← coe_zero, DFunLike.coe_fn_eq]

noncomputable instance : DecidableEq (AddChar A M) := Classical.decEq _

end

section
variable [AddCommGroup A] [DivisionCommMonoid M]

@[simp] lemma zsmul_apply (n : ℤ) (ψ : AddChar A M) (a : A) : (n • ψ) a = ψ a ^ n := by
  cases n
  · simp
  · simp [-neg_apply, neg_apply']

end
end AddChar
