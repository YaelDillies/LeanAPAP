import Mathlib.Data.Nat.Choose.Multinomial

#align_import mathlib.data.nat.choose.multinomial

open Finset

open scoped BigOperators Nat

variable {α : Type*} {s : Finset α} {f : α → ℕ} {a b : α} {n : ℕ}

namespace Nat

lemma multinomial_cons (ha : a ∉ s) :
    multinomial (s.cons a ha) f = (f a + ∑ i in s, f i).choose (f a) * multinomial s f := by
  rw [multinomial, Nat.div_eq_iff_eq_mul_left _ (prod_factorial_dvd_factorial_sum _ _), prod_cons,
    multinomial, mul_assoc, mul_left_comm _ (f a)!,
    Nat.div_mul_cancel (prod_factorial_dvd_factorial_sum _ _), ← mul_assoc, Nat.choose_symm_add,
    Nat.add_choose_mul_factorial_mul_factorial, sum_cons]
  exact prod_pos λ i hi => by positivity

-- TODO: Fix implicitness to `nat.multinomial_insert`
lemma multinomial_insert' [DecidableEq α] (ha : a ∉ s) :
    multinomial (insert a s) f = (f a + ∑ i in s, f i).choose (f a) * multinomial s f := by
  rw [← cons_eq_insert _ _ ha, multinomial_cons]

end Nat
