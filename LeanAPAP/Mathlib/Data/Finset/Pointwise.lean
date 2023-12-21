import Mathlib.Data.Finset.Pointwise
import LeanAPAP.Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.GroupAction.Pi

open Finset
open scoped BigOperators Pointwise

namespace Finset
variable {α : Type*} [DecidableEq α]

section CommMonoid
variable [CommMonoid α] {ι : Type*} [DecidableEq ι]

@[to_additive (attr := simp)] lemma prod_inv_index [InvolutiveInv ι] (s : Finset ι) (f : ι → α) :
    ∏ i in s⁻¹, f i = ∏ i in s, f i⁻¹ := prod_image $ inv_injective.injOn _

@[to_additive existing, simp] lemma prod_neg_index [InvolutiveNeg ι] (s : Finset ι) (f : ι → α) :
    ∏ i in -s, f i = ∏ i in s, f (-i) := prod_image $ neg_injective.injOn _

end CommMonoid

section AddCommMonoid
variable [AddCommMonoid α] {ι : Type*} [DecidableEq ι]

@[to_additive existing, simp] lemma sum_inv_index [InvolutiveInv ι] (s : Finset ι) (f : ι → α) :
    ∑ i in s⁻¹, f i = ∑ i in s, f i⁻¹ := sum_image $ inv_injective.injOn _

end AddCommMonoid

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
variable {ι : Type*} {α β : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (α i)]
  [∀ i, DecidableEq (β i)]

@[to_additive]
lemma piFinset_mul [∀ i, Mul (α i)] (s t : ∀ i, Finset (α i)) :
    piFinset (s * t) = piFinset s * piFinset t := piFinset_image₂ _ _ _

@[to_additive]
lemma piFinset_mul' [∀ i, Mul (α i)] (s t : ∀ i, Finset (α i)) :
    piFinset (fun i ↦ s i * t i) = piFinset s * piFinset t := piFinset_image₂ _ _ _

@[to_additive]
lemma piFinset_div [∀ i, Div (α i)] (s t : ∀ i, Finset (α i)) :
    piFinset (s / t) = piFinset s / piFinset t := piFinset_image₂ _ _ _

@[to_additive]
lemma piFinset_div' [∀ i, Div (α i)] (s t : ∀ i, Finset (α i)) :
    piFinset (fun i ↦ s i / t i) = piFinset s / piFinset t := piFinset_image₂ _ _ _

@[to_additive (attr := simp)]
lemma piFinset_inv [∀ i, Inv (α i)] (s : ∀ i, Finset (α i)) :
    piFinset s⁻¹ = (piFinset s)⁻¹ := piFinset_image _ _

@[to_additive (attr := simp)]
lemma piFinset_inv' [∀ i, Inv (α i)] (s : ∀ i, Finset (α i)) :
    piFinset (fun i ↦ (s i)⁻¹) = (piFinset s)⁻¹ := piFinset_image _ _

@[to_additive]
lemma piFinset_smul [∀ i, SMul (α i) (β i)] (s : ∀ i, Finset (α i)) (t : ∀ i, Finset (β i)) :
    piFinset (s • t) = piFinset s • piFinset t := piFinset_image₂ _ _ _

@[to_additive]
lemma piFinset_smul' [∀ i, SMul (α i) (β i)] (s : ∀ i, Finset (α i)) (t : ∀ i, Finset (β i)) :
    piFinset (fun i ↦ s i • t i) = piFinset s • piFinset t := piFinset_image₂ _ _ _

@[to_additive]
lemma piFinset_smul_finset [∀ i, SMul (α i) (β i)] (a : ∀ i, α i) (s : ∀ i, Finset (β i)) :
    piFinset (a • s) = a • piFinset s := piFinset_image _ _

@[to_additive]
lemma piFinset_smul_finset' [∀ i, SMul (α i) (β i)] (a : ∀ i, α i) (s : ∀ i, Finset (β i)) :
    piFinset (fun i ↦ a i • s i) = a • piFinset s := piFinset_image _ _

end Fintype
