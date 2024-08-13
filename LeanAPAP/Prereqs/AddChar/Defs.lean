import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.RCLike.Basic

open Finset hiding card
open Fintype (card)
open Function
open scoped ComplexConjugate DirectSum NNRat

variable {G H R : Type*}

namespace AddChar
section AddGroup
variable [AddGroup G]

section NormedField
variable [NormedField R]

@[simp] lemma coe_ne_zero (ψ : AddChar G R) : (ψ : G → R) ≠ 0 :=
  ne_iff.2 ⟨0, fun h ↦ by simpa only [h, Pi.zero_apply, zero_ne_one] using map_zero_eq_one ψ⟩

variable [Finite G]

@[simp] lemma norm_apply (ψ : AddChar G R) (x : G) : ‖ψ x‖ = 1 :=
  (ψ.toMonoidHom.isOfFinOrder $ isOfFinOrder_of_finite _).norm_eq_one

end NormedField

section RCLike
variable [RCLike R]

lemma inv_apply_eq_conj [Finite G] (ψ : AddChar G R) (x : G) : (ψ x)⁻¹ = conj (ψ x) :=
  RCLike.inv_eq_conj $ norm_apply _ _

end RCLike
end AddGroup

section AddCommGroup
variable [AddCommGroup G]

section RCLike
variable [RCLike R] {ψ₁ ψ₂ : AddChar G R}

lemma map_neg_eq_conj [Finite G] (ψ : AddChar G R) (x : G) : ψ (-x) = conj (ψ x) := by
  rw [map_neg_eq_inv, RCLike.inv_eq_conj $ norm_apply _ _]

end RCLike

end AddCommGroup

section DirectSum
variable {ι : Type*} {π : ι → Type*} [DecidableEq ι] [∀ i, AddCommGroup (π i)] [CommMonoid R]

/-- Direct sum of additive characters. -/
protected def directSum (ψ : ∀ i, AddChar (π i) R) : AddChar (⨁ i, π i) R :=
  AddChar.toAddMonoidHomEquiv.symm
    (DirectSum.toAddMonoid fun i ↦ toAddMonoidHomEquiv (ψ i) : (⨁ i, π i) →+ Additive R)

lemma directSum_injective :
    Injective (AddChar.directSum : (∀ i, AddChar (π i) R) → AddChar (⨁ i, π i) R) := by
  refine AddChar.toAddMonoidHomEquiv.symm.injective.comp $ DirectSum.toAddMonoid_injective.comp ?_
  rintro ψ χ h
  simpa [Function.funext_iff] using h

end DirectSum
end AddChar
