import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Data.Finset.Pointwise

open scoped BigOperators Pointwise

variable {α : Type*} [DecidableEq α]

namespace Finset
section Mul
variable [Mul α] {s s₁ s₂ t t₁ t₂ : Finset α}

notation3:max "Eₘ[" s ", " t "]" => Finset.multiplicativeEnergy s t
notation3:max "E[" s ", " t "]" => Finset.additiveEnergy s t
notation3:max "Eₘ[" s "]" => Finset.multiplicativeEnergy s s
notation3:max "E[" s "]" => Finset.additiveEnergy s s

@[to_additive additiveEnergy_eq_card_filter]
lemma multiplicativeEnergy_eq_card_filter (s t : Finset α) :
    Eₘ[s, t] = (((s ×ˢ t) ×ˢ s ×ˢ t).filter fun ((a, b), c, d) ↦ a * b = c * d).card := by
  refine Finset.card_congr (fun ((a, b), c, d) _ ↦ ((a, c), b, d)) (by aesop) (by aesop)
    fun ((a, b), c, d) h ↦ ⟨((a, c), b, d), by simpa [and_and_and_comm] using h⟩

@[to_additive additiveEnergy_eq_sum_sq']
lemma multiplicativeEnergy_eq_sum_sq' (s t : Finset α) :
    Eₘ[s, t] = ∑ a in s * t, ((s ×ˢ t).filter fun (x, y) ↦ x * y = a).card ^ 2 := by
  simp_rw [multiplicativeEnergy_eq_card_filter, sq, ← card_product]
  rw [← card_disjiUnion]
  -- The `swap`, `ext` and `simp` calls significantly reduce heartbeats
  swap
  · simp [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left]
    aesop
  · congr
    ext
    simp
    aesop (add unsafe mul_mem_mul)

@[to_additive additiveEnergy_eq_sum_sq]
lemma multiplicativeEnergy_eq_sum_sq [Fintype α] (s t : Finset α) :
    Eₘ[s, t] = ∑ a, ((s ×ˢ t).filter fun (x, y) ↦ x * y = a).card ^ 2 := by
  rw [multiplicativeEnergy_eq_sum_sq']
  exact Fintype.sum_subset $ by aesop (add simp [filter_eq_empty_iff, mul_mem_mul])

@[to_additive card_sq_le_card_mul_additiveEnergy]
lemma card_sq_le_card_mul_multiplicativeEnergy (s t u : Finset α) :
    ((s ×ˢ t).filter fun (a, b) ↦ a * b ∈ u).card ^ 2 ≤ u.card * Eₘ[s, t] := by
  calc
    _ = (∑ c in u, ((s ×ˢ t).filter fun (a, b) ↦ a * b = c).card) ^ 2 := by
        rw [← sum_card_fiberwise_eq_card_filter]
    _ ≤ u.card * ∑ c in u, ((s ×ˢ t).filter fun (a, b) ↦ a * b = c).card ^ 2 := by
        simpa using sum_mul_sq_le_sq_mul_sq (R := ℕ) _ 1 _
    _ ≤ u.card * ∑ c in s * t, ((s ×ˢ t).filter fun (a, b) ↦ a * b = c).card ^ 2 := by
        refine mul_le_mul_left' (sum_le_sum_of_ne_zero ?_) _
        aesop (add simp [filter_eq_empty_iff]) (add unsafe mul_mem_mul)
    _ = u.card * Eₘ[s, t] := by rw [multiplicativeEnergy_eq_sum_sq']

@[to_additive le_card_add_mul_additiveEnergy]
lemma le_card_add_mul_multiplicativeEnergy (s t : Finset α) :
    s.card ^ 2 * t.card ^ 2 ≤ (s * t).card * Eₘ[s, t] :=
  calc
    _ = ((s ×ˢ t).filter fun (a, b) ↦ a * b ∈ s * t).card ^ 2 := by
      rw [filter_eq_self.2, card_product, mul_pow]; aesop (add unsafe mul_mem_mul)
    _ ≤ (s * t).card * Eₘ[s, t] := card_sq_le_card_mul_multiplicativeEnergy _ _ _

end Mul
end Finset
