import Mathlib.Algebra.BigOperators.Expect
import LeanAPAP.Prereqs.Function.Indicator.Defs
import LeanAPAP.Prereqs.Inner.Discrete.Defs

open Finset MeasureTheory
open scoped BigOperators ComplexConjugate

variable {α R : Type*} [Fintype α] [DecidableEq α]

section CommSemiring
variable [CommSemiring R] [StarRing R]

lemma indicate_dL2Inner (s : Finset α) (f : α → R) : ⟪𝟭 s, f⟫_[R] = ∑ i ∈ s, f i := by
  simp [dL2Inner, indicate_apply]

lemma dL2Inner_indicate (f : α → R) (s : Finset α) : ⟪f, 𝟭 s⟫_[R] = ∑ i ∈ s, conj (f i) := by
  simp [dL2Inner, indicate_apply]

end CommSemiring

section Semifield
variable [Semifield R] [CharZero R] [StarRing R]

lemma mu_dL2Inner (s : Finset α) (f : α → R) : ⟪μ s, f⟫_[R] = 𝔼 i ∈ s, f i := by
  simp [dL2Inner, indicate_apply]; simp [mu_apply, expect_eq_sum_div_card, mul_sum, div_eq_inv_mul]

lemma dL2Inner_mu (f : α → R) (s : Finset α) : ⟪f, μ s⟫_[R] = 𝔼 i ∈ s, conj (f i) := by
  simp [dL2Inner, indicate_apply]; simp [mu_apply, expect_eq_sum_div_card, sum_mul, div_eq_mul_inv]

end Semifield
