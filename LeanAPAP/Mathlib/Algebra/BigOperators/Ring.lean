import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod

/-!
## TODO

More explicit arguments to `finset.mul_sum`/`finset.sum_mul`
-/

open scoped BigOperators

namespace Finset
variable {ι α β : Type*}

-- TODO: This is a copy of `finset.prod_univ_sum` with patched universe variables
/-- The product over `univ` of a sum can be written as a sum over the product of sets,
`fintype.piFinset`. `finset.prod_sum` is an alternative statement when the product is not
over `univ` -/
lemma prod_univ_sum' [DecidableEq α] [Fintype α] [CommSemiring β] {δ : α → Type*}
    [∀ a, DecidableEq (δ a)] {t : ∀ a, Finset (δ a)} {f : ∀ a, δ a → β} :
    ∏ a, ∑ b in t a, f a b = ∑ p in Fintype.piFinset t, ∏ x, f x (p x) := by
  simp only [Finset.prod_attach_univ, prod_sum, Finset.sum_univ_pi]

lemma sum_prod_piFinset [DecidableEq ι] [Fintype ι] [CommSemiring β] (s : Finset α)
    (g : ι → α → β) :
    ∑ f in Fintype.piFinset λ _ : ι ↦ s, ∏ i, g i (f i) = ∏ i, ∑ x in s, g i x := by
  classical rw [←@Finset.prod_univ_sum' ι]

section CommMonoid
variable [CommMonoid β]

lemma pow_sum (s : Finset α) (f : α → ℕ) (m : β) : ∏ i in s, m ^ f i = m ^ ∑ i in s, f i := by
  induction' s using Finset.cons_induction_on with a s has ih <;> simp [*, pow_add]

end CommMonoid

section CommSemiring
variable [CommSemiring β]

lemma sum_pow' (s : Finset α) (f : α → β) (n : ℕ) :
    (∑ a in s, f a) ^ n = ∑ p in Fintype.piFinset λ _i : Fin n ↦ s, ∏ i, f (p i) := by
  classical convert @prod_univ_sum' (Fin n) _ _ _ _ _ _ (λ _i ↦ s) λ _i d ↦ f d; simp

end CommSemiring

end Finset

namespace Fintype
variable {α β : Type*} [Fintype α] [CommSemiring β]

lemma sum_pow (f : α → β) (n : ℕ) : (∑ a, f a) ^ n = ∑ p : Fin n → α, ∏ i, f (p i) := by
  simp [Finset.sum_pow']

lemma sum_mul_sum {ι₁ : Type*} {ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (f₁ : ι₁ → β)
    (f₂ : ι₂ → β) : (∑ x₁, f₁ x₁) * ∑ x₂, f₂ x₂ = ∑ p : ι₁ × ι₂, f₁ p.1 * f₂ p.2 :=
  Finset.sum_mul_sum _ _ _ _

end Fintype

open Finset

namespace Nat
variable {α : Type*} {s : Finset α} {f : α → ℕ} {n : ℕ}

protected lemma sum_div (hf : ∀ i ∈ s, n ∣ f i) : (∑ i in s, f i) / n = ∑ i in s, f i / n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  rw [Nat.div_eq_iff_eq_mul_left hn (dvd_sum hf), sum_mul]
  refine' sum_congr rfl λ s hs ↦ _
  rw [Nat.div_mul_cancel (hf _ hs)]

end Nat
