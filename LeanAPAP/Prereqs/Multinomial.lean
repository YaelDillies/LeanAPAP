import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorial.DoubleFactorial

open Finset

variable {K : Type*} {s : Finset K} {f f' : K → ℕ}
namespace Nat

lemma double_multinomial :
    (multinomial s fun i ↦ 2 * f i) ≤ ((∑ i in s, f i) ^ ∑ i in s, f i) * multinomial s f := by
  rw [multinomial, multinomial, ←mul_sum]
  refine Nat.div_le_of_le_mul' ?_
  rw [←mul_assoc, ←Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum _ _),
    Nat.le_div_iff_mul_le]
  swap
  · exact prod_pos fun i _ ↦ by positivity
  refine (Nat.mul_le_mul_right _ $ factorial_two_mul_le _).trans ?_
  rw [mul_pow, mul_comm, ←mul_assoc, ←mul_assoc]
  refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
  rw [←Finset.prod_pow_eq_pow_sum, ←prod_mul_distrib]
  refine prod_le_prod' fun i _ ↦ ?_
  rw [mul_comm, ←doubleFactorial_two_mul]
  exact doubleFactorial_le_factorial _

end Nat
