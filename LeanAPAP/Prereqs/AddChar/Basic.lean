import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Group.AddChar
import LeanAPAP.Prereqs.Inner.Weighted

open Finset hiding card
open Fintype (card)
open Function RCLike
open scoped BigOperators ComplexConjugate DirectSum

variable {G H R : Type*}

namespace AddChar
section AddGroup
variable [AddGroup G]

section Semifield
variable [Fintype G] [Semifield R] [IsDomain R] [CharZero R] {ψ : AddChar G R}

lemma expect_eq_ite (ψ : AddChar G R) : 𝔼 a, ψ a = if ψ = 0 then 1 else 0 := by
  split_ifs with h
  · simp [h, card_univ]
  obtain ⟨x, hx⟩ := ne_one_iff.1 h
  refine eq_zero_of_mul_eq_self_left hx ?_
  rw [Finset.mul_expect]
  exact Fintype.expect_equiv (Equiv.addLeft x) _ _ fun y ↦ (map_add_eq_mul _ _ _).symm

lemma expect_eq_zero_iff_ne_zero : 𝔼 x, ψ x = 0 ↔ ψ ≠ 0 := by
  rw [expect_eq_ite, one_ne_zero.ite_eq_right_iff]

lemma expect_ne_zero_iff_eq_zero : 𝔼 x, ψ x ≠ 0 ↔ ψ = 0 := expect_eq_zero_iff_ne_zero.not_left

end Semifield

section RCLike
variable [RCLike R] [Fintype G]

lemma wInner_compact_self (ψ : AddChar G R) : ⟪(ψ : G → R), ψ⟫ₙ_[R] = 1 := by
  simp [wInner_compact_eq_expect, ψ.norm_apply, RCLike.conj_mul]

end RCLike
end AddGroup

section AddCommGroup
variable [AddCommGroup G]

section RCLike
variable [RCLike R] {ψ₁ ψ₂ : AddChar G R}

lemma wInner_compact_eq_boole [Fintype G] (ψ₁ ψ₂ : AddChar G R) :
    ⟪(ψ₁ : G → R), ψ₂⟫ₙ_[R] = if ψ₁ = ψ₂ then 1 else 0 := by
  split_ifs with h
  · rw [h, wInner_compact_self]
  have : ψ₁⁻¹ * ψ₂ ≠ 1 := by rwa [Ne, inv_mul_eq_one]
  simp_rw [wInner_compact_eq_expect, RCLike.inner_apply, ← inv_apply_eq_conj]
  simpa [map_neg_eq_inv] using expect_eq_zero_iff_ne_zero.2 this

lemma wInner_compact_eq_zero_iff_ne [Fintype G] : ⟪(ψ₁ : G → R), ψ₂⟫ₙ_[R] = 0 ↔ ψ₁ ≠ ψ₂ := by
  rw [wInner_compact_eq_boole, one_ne_zero.ite_eq_right_iff]

lemma wInner_compact_eq_one_iff_eq [Fintype G] : ⟪(ψ₁ : G → R), ψ₂⟫ₙ_[R] = 1 ↔ ψ₁ = ψ₂ := by
  rw [wInner_compact_eq_boole, one_ne_zero.ite_eq_left_iff]

variable (G R)

protected lemma linearIndependent [Finite G] : LinearIndependent R ((⇑) : AddChar G R → G → R) := by
  cases nonempty_fintype G
  exact linearIndependent_of_ne_zero_of_wInner_compact_eq_zero AddChar.coe_ne_zero fun ψ₁ ψ₂ ↦
    wInner_compact_eq_zero_iff_ne.2

noncomputable instance instFintype [Finite G] : Fintype (AddChar G R) :=
  @Fintype.ofFinite _ (AddChar.linearIndependent G R).finite

@[simp] lemma card_addChar_le [Fintype G] : card (AddChar G R) ≤ card G := by
  simpa only [Module.finrank_fintype_fun_eq_card] using
    (AddChar.linearIndependent G R).fintype_card_le_finrank

end RCLike
end AddCommGroup
end AddChar
