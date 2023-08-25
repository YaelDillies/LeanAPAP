import Mathlib.Data.Finset.NatAntidiagonal

#align_import mathlib.data.finset.nat_antidiagonal

open Finset

variable {n : ℕ} {p q : ℕ × ℕ}

namespace Finset

namespace Nat

lemma swap_mem_antidiagonal (hp : p ∈ antidiagonal n) : p.symm ∈ antidiagonal n := by
  rw [← map_swap_antidiagonal]; exact mem_map_of_mem _ hp

/-- A point in the antidiagonal is determined by its second co-ordinate. cf `antidiagonal_congr'` -/
lemma antidiagonal_congr' (hp : p ∈ antidiagonal n) (hq : q ∈ antidiagonal n) :
    p = q ↔ p.2 = q.2 := by
  rw [← Prod.swap_inj]
  exact antidiagonal_congr (swap_mem_antidiagonal hp) (swap_mem_antidiagonal hq)

lemma antidiagonal_eq_map :
    n.antidiagonal = (range (n + 1)).map ⟨λ i => (i, n - i), λ i j h => (Prod.ext_iff.1 h).1⟩ := rfl

lemma antidiagonal_eq_image : n.antidiagonal = (range (n + 1)).image λ i => (i, n - i) := by
  simp only [antidiagonal_eq_map, map_eq_image, Function.Embedding.coeFn_mk]

end Nat

end Finset
