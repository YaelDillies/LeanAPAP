import LeanAPAP.Mathlib.Algebra.BigOperators.Ring
import LeanAPAP.Mathlib.Data.Finset.NatAntidiagonal
import LeanAPAP.Mathlib.Data.Nat.Choose.Multinomial
import LeanAPAP.Mathlib.Data.Nat.Factorial.Basic
import LeanAPAP.Mathlib.Data.Nat.Factorial.DoubleFactorial
import LeanAPAP.Prereqs.Cut

#align_import prereqs.multinomial

/-!

## TODO

Rename `nat.multinomial_nil` to `nat.multinomial_empty`
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
  rw [sum_insert has, cut_insert _ _ _ has, sum_bUnion (cut_insert_disjoint_bUnion _ _ _ has)]
  dsimp
  simp only [sum_map, Function.Embedding.coeFn_mk, Pi.add_apply, multinomial_insert' has,
    Pi.add_apply, eq_self_iff_true, if_true, Nat.cast_mul, prod_insert has, eq_self_iff_true,
    if_true, sum_add_distrib, sum_ite_eq', has, if_false, add_zero]
  suffices
    ∀ p : ℕ × ℕ,
      p ∈ n.antidiagonal →
        ∑ f in cut s p.snd,
            ((f a + p.fst + s.sum f).choose (f a + p.fst) : β) *
                multinomial s (f + λ t => ite (t = a) p.fst 0) *
              (x a ^ (f a + p.fst) * ∏ t : α in s, x t ^ (f t + ite (t = a) p.fst 0)) =
          ∑ f in cut s p.snd,
            n.choose p.fst * multinomial s f * (x a ^ p.fst * ∏ t : α in s, x t ^ f t)
    by
    rw [sum_congr rfl this]
    simp only [nat.antidiagonal_eq_map, sum_map, Function.Embedding.coeFn_mk]
    rw [add_pow]
    simp only [ih, sum_mul, mul_sum]
    refine' sum_congr rfl λ i hi => sum_congr rfl λ f hf => _
    ac_rfl
  refine' λ p hp => sum_congr rfl λ f hf => _
  rw [mem_cut] at hf
  rw [hf.2 _ has, zero_add, hf.1]
  congr 2
  · rw [nat.mem_antidiagonal.1 hp]
  · rw [multinomial_congr]
    intro t ht
    rw [Pi.add_apply, if_neg, add_zero]
    exact ne_of_mem_of_not_mem ht has
  refine' prod_congr rfl λ t ht => _
  rw [if_neg, add_zero]
  exact ne_of_mem_of_not_mem ht has

lemma double_multinomial :
    (multinomial s λ i => 2 * f i) ≤ ((∑ i in s, f i) ^ ∑ i in s, f i) * multinomial s f := by
  rw [multinomial, multinomial, ← mul_sum]
  refine' Nat.div_le_of_le_mul' _
  rw [← mul_assoc, ← Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum _ _),
    Nat.le_div_iff_mul_le]
  swap
  · exact prod_pos λ i hi => by positivity
  refine' (Nat.mul_le_mul_right _ factorial_two_mul_le).trans _
  rw [mul_pow, mul_comm, ← mul_assoc, ← mul_assoc]
  refine' Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ _)
  rw [← Finset.pow_sum, ← prod_mul_distrib]
  refine' prod_le_prod' λ i hi => _
  rw [mul_comm, ← double_factorial_two_mul]
  exact double_factorial_le_factorial

end Nat
