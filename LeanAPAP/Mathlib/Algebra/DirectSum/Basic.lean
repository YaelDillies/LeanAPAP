import Mathlib.Algebra.DirectSum.Basic

#align_import mathlib.algebra.direct_sum.basic

open Function

open scoped DirectSum

variable {ι γ : Type*} [DecidableEq ι] {β : ι → Type*} [∀ i, AddCommMonoid (β i)]
  [AddCommMonoid γ]

namespace DirectSum

lemma toAddMonoid_injective : Injective (toAddMonoid : (∀ i, β i →+ γ) → (⨁ i, β i) →+ γ) := by
  rintro f g h
  ext i b
  simpa using FunLike.congr_λ h (DirectSum.of _ i b)

@[simp]
lemma toAddMonoid_inj {f g : ∀ i, β i →+ γ} : toAddMonoid f = toAddMonoid g ↔ f = g :=
  toAddMonoid_injective.eq_iff

end DirectSum
