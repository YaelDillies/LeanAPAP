import LeanAPAP.Mathlib.Algebra.Group.AddChar
import LeanAPAP.Prereqs.Expect.Basic
import LeanAPAP.Prereqs.LpNorm.Discrete.Inner

open Finset hiding card
open Fintype (card)
open Function MeasureTheory
open scoped BigOperators ComplexConjugate DirectSum

variable {G H R : Type*}

namespace AddChar
section AddGroup
variable [AddGroup G]
section RCLike
variable [RCLike R]

protected lemma dL2Inner_self [Fintype G] (ψ : AddChar G R) :
    ⟪(ψ : G → R), ψ⟫_[R] = Fintype.card G := dL2Inner_self_of_norm_eq_one ψ.norm_apply

end RCLike

section Semifield
variable [Fintype G] [Semifield R] [IsDomain R] [CharZero R] {ψ : AddChar G R}

lemma expect_eq_ite (ψ : AddChar G R) : 𝔼 a, ψ a = if ψ = 0 then 1 else 0 := by
  split_ifs with h
  · simp [h, card_univ, univ_nonempty]
  obtain ⟨x, hx⟩ := ne_one_iff.1 h
  refine eq_zero_of_mul_eq_self_left hx ?_
  rw [Finset.mul_expect]
  exact Fintype.expect_equiv (Equiv.addLeft x) _ _ fun y ↦ (map_add_eq_mul _ _ _).symm

lemma expect_eq_zero_iff_ne_zero : 𝔼 x, ψ x = 0 ↔ ψ ≠ 0 := by
  rw [expect_eq_ite, one_ne_zero.ite_eq_right_iff]

lemma expect_ne_zero_iff_eq_zero : 𝔼 x, ψ x ≠ 0 ↔ ψ = 0 := expect_eq_zero_iff_ne_zero.not_left

end Semifield
end AddGroup

section AddCommGroup
variable [AddCommGroup G]

section RCLike
variable [RCLike R] {ψ₁ ψ₂ : AddChar G R}

lemma dL2Inner_eq [Fintype G] (ψ₁ ψ₂ : AddChar G R) :
    ⟪(ψ₁ : G → R), ψ₂⟫_[R] = if ψ₁ = ψ₂ then ↑(card G) else 0 := by
  split_ifs with h
  · rw [h, AddChar.dL2Inner_self]
  have : ψ₁⁻¹ * ψ₂ ≠ 1 := by rwa [Ne, inv_mul_eq_one]
  simp_rw [dL2Inner_eq_sum, ← inv_apply_eq_conj]
  simpa [map_neg_eq_inv] using sum_eq_zero_iff_ne_zero.2 this

lemma dL2Inner_eq_zero_iff_ne [Fintype G] : ⟪(ψ₁ : G → R), ψ₂⟫_[R] = 0 ↔ ψ₁ ≠ ψ₂ := by
  rw [dL2Inner_eq, Ne.ite_eq_right_iff (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]

lemma dL2Inner_eq_card_iff_eq [Fintype G] : ⟪(ψ₁ : G → R), ψ₂⟫_[R] = card G ↔ ψ₁ = ψ₂ := by
  rw [dL2Inner_eq, Ne.ite_eq_left_iff (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]

variable (G R)

protected lemma linearIndependent [Finite G] : LinearIndependent R ((⇑) : AddChar G R → G → R) := by
  cases nonempty_fintype G
  exact linearIndependent_of_ne_zero_of_dL2Inner_eq_zero AddChar.coe_ne_zero fun ψ₁ ψ₂ ↦
    dL2Inner_eq_zero_iff_ne.2

noncomputable instance instFintype [Finite G] : Fintype (AddChar G R) :=
  @Fintype.ofFinite _ (AddChar.linearIndependent G R).finite

@[simp] lemma card_addChar_le [Fintype G] : card (AddChar G R) ≤ card G := by
  simpa only [FiniteDimensional.finrank_fintype_fun_eq_card] using
    (AddChar.linearIndependent G R).fintype_card_le_finrank

end RCLike
end AddCommGroup
end AddChar
