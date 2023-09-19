import Mathlib.Data.Finset.Pointwise
import LeanAPAP.Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.GroupAction.Pi

open Finset

open scoped Pointwise

namespace Finset
variable {α : Type*} [DecidableEq α]

section InvolutiveInv
variable [InvolutiveInv α] {s : Finset α} {a : α}

@[to_additive (attr := simp)]
lemma mem_inv' : a ∈ s⁻¹ ↔ a⁻¹ ∈ s := by simp [mem_inv, inv_eq_iff_eq_inv]

@[to_additive (attr := simp)]
lemma inv_univ [Fintype α] : (univ : Finset α)⁻¹ = univ := by ext; simp

end InvolutiveInv

section DivisionMonoid
variable [DivisionMonoid α] [Fintype α]

@[to_additive (attr := simp)]
lemma univ_div_univ : (univ / univ : Finset α) = univ := by simp [div_eq_mul_inv]

end DivisionMonoid

end Finset

namespace Fintype
variable {ι : Type*} {α β : ι → Type*} [Fintype ι] [DecidableEq ι]

@[to_additive]
lemma piFinset_mul [∀ i, DecidableEq (α i)] [∀ i, Mul (α i)] (s t : ∀ i, Finset (α i)) :
    piFinset (s * t) = Fintype.piFinset s * Fintype.piFinset t :=
  Fintype.piFinset_image₂ _ _ _

@[to_additive]
lemma piFinset_div [∀ i, DecidableEq (α i)] [∀ i, Div (α i)] (s t : ∀ i, Finset (α i)) :
    piFinset (s / t) = Fintype.piFinset s / Fintype.piFinset t :=
  Fintype.piFinset_image₂ _ _ _

@[to_additive]
lemma piFinset_smul [∀ i, DecidableEq (β i)] [∀ i, SMul (α i) (β i)] (s : ∀ i, Finset (α i))
    (t : ∀ i, Finset (β i)) : piFinset (s • t) = Fintype.piFinset s • Fintype.piFinset t :=
  Fintype.piFinset_image₂ _ _ _

@[to_additive]
lemma piFinset_smul_finset [∀ i, DecidableEq (β i)] [∀ i, SMul (α i) (β i)] (a : ∀ i, α i)
    (s : ∀ i, Finset (β i)) : piFinset (a • s) = a • Fintype.piFinset s :=
  Fintype.piFinset_image _ _

end Fintype
