import LeanAPAP.Mathlib.Algebra.Group.AddChar
import LeanAPAP.Prereqs.Discrete.Convolution.Basic
import LeanAPAP.Prereqs.Discrete.LpNorm.Basic

/-!
### TODO

Rename
* `map_add_mul` → `map_add_eq_mul`
* `map_zero_one` → `map_zero_eq_one`
* `map_nsmul_pow` → `map_nsmul_eq_pow`
-/

open Finset hiding card
open Fintype (card)
open Function
open scoped BigOperators ComplexConjugate DirectSum NNRat

variable {G H R : Type*}

namespace AddChar
section AddGroup
variable [AddGroup G]

section NormedField
variable [Finite G] [NormedField R]

@[simp] lemma norm_apply (ψ : AddChar G R) (x : G) : ‖ψ x‖ = 1 :=
  (ψ.toMonoidHom.isOfFinOrder $ isOfFinOrder_of_finite _).norm_eq_one

@[simp] lemma coe_ne_zero (ψ : AddChar G R) : (ψ : G → R) ≠ 0 :=
  Function.ne_iff.2 ⟨0, fun h ↦ by simpa only [h, Pi.zero_apply, zero_ne_one] using map_zero_one ψ⟩

end NormedField

section RCLike
variable [RCLike R]

lemma inv_apply_eq_conj [Finite G] (ψ : AddChar G R) (x : G) : (ψ x)⁻¹ = conj (ψ x) :=
  RCLike.inv_eq_conj $ norm_apply _ _

protected lemma l2Inner_self [Fintype G] (ψ : AddChar G R) :
    ⟪(ψ : G → R), ψ⟫_[R] = Fintype.card G := l2Inner_self_of_norm_eq_one ψ.norm_apply

end RCLike

section Semifield
variable [Fintype G] [Semifield R] [IsDomain R] [CharZero R] {ψ : AddChar G R}

lemma expect_eq_ite (ψ : AddChar G R) : 𝔼 a, ψ a = if ψ = 0 then 1 else 0 := by
  split_ifs with h
  · simp [h, card_univ, univ_nonempty]
  obtain ⟨x, hx⟩ := ne_one_iff.1 h
  refine' eq_zero_of_mul_eq_self_left hx _
  rw [Finset.mul_expect]
  exact Fintype.expect_equiv (Equiv.addLeft x) _ _ fun y ↦ (map_add_mul _ _ _).symm

lemma expect_eq_zero_iff_ne_zero : 𝔼 x, ψ x = 0 ↔ ψ ≠ 0 := by
  rw [expect_eq_ite, one_ne_zero.ite_eq_right_iff]

lemma expect_ne_zero_iff_eq_zero : 𝔼 x, ψ x ≠ 0 ↔ ψ = 0 := expect_eq_zero_iff_ne_zero.not_left

end Semifield
end AddGroup

section AddCommGroup
variable [AddCommGroup G]

section RCLike
variable [RCLike R] {ψ₁ ψ₂ : AddChar G R}

lemma map_neg_eq_conj [Finite G] (ψ : AddChar G R) (x : G) : ψ (-x) = conj (ψ x) := by
  rw [map_neg_eq_inv, RCLike.inv_eq_conj $ norm_apply _ _]

lemma l2Inner_eq [Fintype G] (ψ₁ ψ₂ : AddChar G R) :
    ⟪(ψ₁ : G → R), ψ₂⟫_[R] = if ψ₁ = ψ₂ then ↑(card G) else 0 := by
  split_ifs with h
  · rw [h, AddChar.l2Inner_self]
  have : ψ₁⁻¹ * ψ₂ ≠ 1 := by rwa [Ne.def, inv_mul_eq_one]
  simp_rw [l2Inner_eq_sum, ←inv_apply_eq_conj]
  simpa [map_neg_eq_inv] using sum_eq_zero_iff_ne_zero.2 this

lemma l2Inner_eq_zero_iff_ne [Fintype G] : ⟪(ψ₁ : G → R), ψ₂⟫_[R] = 0 ↔ ψ₁ ≠ ψ₂ := by
  rw [l2Inner_eq, Ne.ite_eq_right_iff (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]

lemma l2Inner_eq_card_iff_eq [Fintype G] : ⟪(ψ₁ : G → R), ψ₂⟫_[R] = card G ↔ ψ₁ = ψ₂ := by
  rw [l2Inner_eq, Ne.ite_eq_left_iff (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]

variable (G R)

protected lemma linearIndependent [Finite G] : LinearIndependent R ((⇑) : AddChar G R → G → R) := by
  cases nonempty_fintype G
  exact linearIndependent_of_ne_zero_of_l2Inner_eq_zero AddChar.coe_ne_zero fun ψ₁ ψ₂ ↦
    l2Inner_eq_zero_iff_ne.2

noncomputable instance instFintype [Finite G] : Fintype (AddChar G R) :=
  @Fintype.ofFinite _ (AddChar.linearIndependent G R).finite

@[simp] lemma card_addChar_le [Fintype G] : card (AddChar G R) ≤ card G := by
  simpa only [FiniteDimensional.finrank_fintype_fun_eq_card] using
    (AddChar.linearIndependent G R).fintype_card_le_finrank

end RCLike

end AddCommGroup

section DirectSum
variable {ι : Type*} {π : ι → Type*} [DecidableEq ι] [∀ i, AddCommGroup (π i)] [CommMonoid R]

/-- Direct sum of additive characters. -/
protected def directSum (ψ : ∀ i, AddChar (π i) R) : AddChar (⨁ i, π i) R :=
  AddChar.toAddMonoidHomEquiv'.symm
    (DirectSum.toAddMonoid fun i ↦ toAddMonoidHomEquiv' (ψ i) : (⨁ i, π i) →+ Additive R)

lemma directSum_injective :
    Injective (AddChar.directSum : (∀ i, AddChar (π i) R) → AddChar (⨁ i, π i) R) := by
  refine' AddChar.toAddMonoidHomEquiv'.symm.injective.comp $ DirectSum.toAddMonoid_injective.comp _
  rintro ψ χ h
  simpa [Function.funext_iff] using h

end DirectSum
end AddChar
