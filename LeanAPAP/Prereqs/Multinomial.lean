import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import LeanAPAP.Prereqs.Cut

/-!
## TODO

Rename `Nat.multinomial_nil` to `Nat.multinomial_empty`
-/

open Finset Nat

open scoped BigOperators Nat

variable {K : Type*} {s : Finset K} {f f' : K → ℕ}

namespace Nat

lemma multinomial_expansion' {α β : Type*} [DecidableEq α] [CommSemiring β] {s : Finset α}
    {x : α → β} {n : ℕ} :
    (∑ i in s, x i) ^ n = ∑ k in cut s n, multinomial s k * ∏ t in s, x t ^ k t := by
  classical
  -- maybe make cut_cons and use cons_induction
  induction' s using Finset.induction_on with a s has ih generalizing n
  · cases n <;> simp
  rw [sum_insert has, cut_insert _ _ _ has, sum_biUnion (cut_insert_disjoint_bUnion _ _ _ has)]
  simp only [sum_map, Function.Embedding.coeFn_mk, Pi.add_apply, multinomial_insert _ _ has,
    Pi.add_apply, eq_self_iff_true, if_true, Nat.cast_mul, prod_insert has, eq_self_iff_true,
    if_true, sum_add_distrib, sum_ite_eq', has, if_false, add_zero,
      addLeftEmbedding_eq_addRightEmbedding, addRightEmbedding_apply]
  suffices : ∀ p : ℕ × ℕ, p ∈ antidiagonal n →
    ∑ f in cut s p.snd, ((f a + p.fst + s.sum f).choose (f a + p.fst) : β) *
      multinomial s (f + fun t ↦ ite (t = a) p.fst 0) *
        (x a ^ (f a + p.fst) * ∏ t : α in s, x t ^ (f t + ite (t = a) p.fst 0)) =
      ∑ f in cut s p.snd, n.choose p.fst * multinomial s f * (x a ^ p.fst * ∏ t : α in s, x t ^ f t)
  · rw [sum_congr rfl this]
    simp only [Nat.antidiagonal_eq_map, sum_map, Function.Embedding.coeFn_mk]
    rw [add_pow]
    simp only [ih, sum_mul, mul_sum]
    refine' sum_congr rfl fun i _ ↦ sum_congr rfl fun f _ ↦ _
    ac_rfl
  refine' fun p hp ↦ sum_congr rfl fun f hf ↦ _
  rw [mem_cut] at hf
  rw [hf.2 _ has, zero_add, hf.1]
  congr 2
  · rw [mem_antidiagonal.1 hp]
  · rw [multinomial_congr]
    intro t ht
    rw [Pi.add_apply, if_neg, add_zero]
    exact ne_of_mem_of_not_mem ht has
  refine' prod_congr rfl fun t ht ↦ _
  rw [if_neg, add_zero]
  exact ne_of_mem_of_not_mem ht has

lemma double_multinomial :
    (multinomial s fun i ↦ 2 * f i) ≤ ((∑ i in s, f i) ^ ∑ i in s, f i) * multinomial s f := by
  rw [multinomial, multinomial, ←mul_sum]
  refine' Nat.div_le_of_le_mul' _
  rw [←mul_assoc, ←Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum _ _),
    Nat.le_div_iff_mul_le]
  swap
  · exact prod_pos fun i _ ↦ by positivity
  refine' (Nat.mul_le_mul_right _ $ factorial_two_mul_le _).trans _
  rw [mul_pow, mul_comm, ←mul_assoc, ←mul_assoc]
  refine' Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ _)
  rw [←Finset.pow_sum, ←prod_mul_distrib]
  refine' prod_le_prod' fun i _ ↦ _
  rw [mul_comm, ←doubleFactorial_two_mul]
  exact doubleFactorial_le_factorial _

end Nat
