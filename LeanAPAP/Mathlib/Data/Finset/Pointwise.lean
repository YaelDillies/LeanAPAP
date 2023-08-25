import Mathbin.Data.Finset.Pointwise
import Project.Mathlib.Data.Fintype.Pi
import Mathbin.GroupTheory.GroupAction.Pi

#align_import mathlib.data.finset.pointwise

open Finset

open scoped Pointwise

namespace Finset

variable {α : Type _} [DecidableEq α]

section InvolutiveInv

variable [InvolutiveInv α] {s : Finset α} {a : α}

@[simp, to_additive]
theorem mem_inv' : a ∈ s⁻¹ ↔ a⁻¹ ∈ s := by simp [mem_inv, inv_eq_iff_eq_inv]

@[simp, to_additive]
theorem inv_univ [Fintype α] : (univ : Finset α)⁻¹ = univ := by ext <;> simp

end InvolutiveInv

section DivisionMonoid

variable [DivisionMonoid α] [Fintype α]

@[simp, to_additive]
theorem univ_div_univ : (univ / univ : Finset α) = univ := by simp [div_eq_mul_inv]

end DivisionMonoid

end Finset

namespace Fintype

variable {ι : Type _} {α β : ι → Type _} [Fintype ι] [DecidableEq ι]

@[to_additive]
theorem piFinset_hMul [∀ i, DecidableEq (α i)] [∀ i, Mul (α i)] (s t : ∀ i, Finset (α i)) :
    piFinset (s * t) = Fintype.piFinset s * Fintype.piFinset t :=
  Fintype.piFinset_image₂ _ _ _

@[to_additive]
theorem piFinset_div [∀ i, DecidableEq (α i)] [∀ i, Div (α i)] (s t : ∀ i, Finset (α i)) :
    piFinset (s / t) = Fintype.piFinset s / Fintype.piFinset t :=
  Fintype.piFinset_image₂ _ _ _

@[to_additive]
theorem piFinset_smul [∀ i, DecidableEq (β i)] [∀ i, SMul (α i) (β i)] (s : ∀ i, Finset (α i))
    (t : ∀ i, Finset (β i)) : piFinset (s • t) = Fintype.piFinset s • Fintype.piFinset t :=
  Fintype.piFinset_image₂ _ _ _

@[to_additive]
theorem piFinset_smul_finset [∀ i, DecidableEq (β i)] [∀ i, SMul (α i) (β i)] (a : ∀ i, α i)
    (s : ∀ i, Finset (β i)) : piFinset (a • s) = a • Fintype.piFinset s :=
  Fintype.piFinset_image _ _

end Fintype

