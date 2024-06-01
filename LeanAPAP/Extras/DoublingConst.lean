import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Data.Finset.Pointwise
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Positivity.Finset

open Finset
open scoped Pointwise

namespace Finset
section Group
variable {G : Type*} [Group G] [DecidableEq G] {K L : ℝ} {A B : Finset G} {a : G}

/-- The doubling constant `σₘ[A, B]` of two finsets `A` and `B` in a group is `|A * B| / |A|`.

The notation `σₘ[A, B]` is available in scope `Combinatorics.Additive`. -/
@[to_additive
"The doubling constant `σ[A, B]` of two finsets `A` and `B` in a group is `|A + B| / |A|`.

The notation `σ[A, B]` is available in scope `Combinatorics.Additive`."]
def mulConst (A B : Finset G) : ℚ≥0 := (A * B).card / A.card

/-- The difference constant `δₘ[A, B]` of two finsets `A` and `B` in a group is `|A / B| / |A|`.

The notation `δₘ[A, B]` is available in scope `Combinatorics.Additive`. -/
@[to_additive
"The difference constant `σ[A, B]` of two finsets `A` and `B` in a group is `|A - B| / |A|`.

The notation `δ[A, B]` is available in scope `Combinatorics.Additive`."]
def divConst (A B : Finset G) : ℚ≥0 := (A / B).card / A.card

/-- The doubling constant `σₘ[A, B]` of two finsets `A` and `B` in a group is `|A * B| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "σₘ[" A ", " B "]" => Finset.mulConst A B

/-- The doubling constant `σₘ[A]` of a finset `A` in a group is `|A * A| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "σₘ[" A "]" => Finset.mulConst A A

/-- The doubling constant `σ[A, B]` of two finsets `A` and `B` in a group is `|A + B| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "σ[" A ", " B "]" => Finset.addConst A B

/-- The doubling constant `σ[A]` of a finset `A` in a group is `|A + A| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "σ[" A "]" => Finset.addConst A A

/-- The doubling constant `σₘ[A, B]` of two finsets `A` and `B` in a group is `|A / B| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "δₘ[" A ", " B "]" => Finset.divConst A B

/-- The doubling constant `σₘ[A]` of a finset `A` in a group is `|A / A| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "δₘ[" A "]" => Finset.divConst A A

/-- The doubling constant `σ[A, B]` of two finsets `A` and `B` in a group is `|A - B| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "δ[" A ", " B "]" => Finset.subConst A B

/-- The doubling constant `σ[A]` of a finset `A` in a group is `|A - A| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "δ[" A "]" => Finset.subConst A A

open scoped Combinatorics.Additive

@[to_additive (attr := simp)]
lemma mulConst_mul_card (A B : Finset G) : σₘ[A, B] * A.card = (A * B).card := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  · exact div_mul_cancel₀ _ (by positivity)

@[to_additive (attr := simp)]
lemma card_mul_mulConst (A B : Finset G) : A.card * σₘ[A, B] = (A * B).card := by
  rw [mul_comm, mulConst_mul_card]

@[to_additive (attr := simp)]
lemma divConst_mul_card (A B : Finset G) : δₘ[A, B] * A.card = (A / B).card := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  · exact div_mul_cancel₀ _ (by positivity)

@[to_additive (attr := simp)]
lemma card_mul_divConst (A B : Finset G) : A.card * δₘ[A, B] = (A / B).card := by
  rw [mul_comm, divConst_mul_card]

@[to_additive (attr := simp)]
lemma mulConst_empty_left (B : Finset G) : σₘ[∅, B] = 0 := by simp [mulConst]

@[to_additive (attr := simp)]
lemma divConst_empty_left (B : Finset G) : δₘ[∅, B] = 0 := by simp [divConst]

@[to_additive (attr := simp)]
lemma mulConst_empty_right (A : Finset G) : σₘ[A, ∅] = 0 := by simp [mulConst]

@[to_additive (attr := simp)]
lemma divConst_empty_right (A : Finset G) : δₘ[A, ∅] = 0 := by simp [divConst]

@[to_additive (attr := simp)]
lemma mulConst_inv_right (A B : Finset G) : σₘ[A, B⁻¹] = δₘ[A, B] := by
  rw [mulConst, divConst, ← div_eq_mul_inv]

@[to_additive (attr := simp)]
lemma divConst_inv_right (A B : Finset G) : δₘ[A, B⁻¹] = σₘ[A, B] := by
  rw [mulConst, divConst, div_inv_eq_mul]

end Group

open scoped Combinatorics.Additive

section CommGroup
variable {G : Type*} [CommGroup G] [DecidableEq G] {K L : ℝ} {A B : Finset G} {a : G}

@[to_additive (attr := simp)]
lemma mulConst_inv_left (A B : Finset G) : σₘ[A⁻¹, B] = δₘ[A, B] := by
  rw [mulConst, divConst, card_inv, ← card_inv, mul_inv_rev, inv_inv, inv_mul_eq_div]

@[to_additive (attr := simp)]
lemma divConst_inv_left (A B : Finset G) : δₘ[A⁻¹, B] = σₘ[A, B] := by
  rw [mulConst, divConst, card_inv, ← card_inv, inv_div, div_inv_eq_mul, mul_comm]

/-- If `A` has small difference, then it has small doubling, with the constant squared.

This is a consequence of the Ruzsa triangle inequality. -/
@[to_additive
"If `A` has small difference, then it has small doubling, with the constant squared.

This is a consequence of the Ruzsa triangle inequality."]
lemma mulConst_le_divConst_sq : σₘ[A] ≤ δₘ[A] ^ 2 := by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℚ≥0) < A.card * A.card)
  calc
    _ = (A * A).card * (A.card : ℚ≥0) := by rw [← mul_assoc, mulConst_mul_card]
    _ ≤ (A / A).card * (A / A).card := by
      norm_cast; exact card_mul_mul_le_card_div_mul_card_div _ _ _
    _ = _ := by rw [← divConst_mul_card]; ring

/-- If `A` has small doubling, then it has small difference, with the constant squared.

This is a consequence of the Ruzsa triangle inequality. -/
@[to_additive
"If `A` has small doubling, then it has small difference, with the constant squared.

This is a consequence of the Ruzsa triangle inequality."]
lemma divConst_le_mulConst_sq : δₘ[A] ≤ σₘ[A] ^ 2 := by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℚ≥0) < A.card * A.card)
  calc
    _ = (A / A).card * (A.card : ℚ≥0) := by rw [← mul_assoc, divConst_mul_card]
    _ ≤ (A * A).card * (A * A).card := by
      norm_cast; exact card_div_mul_le_card_mul_mul_card_mul _ _ _
    _ = _ := by rw [← mulConst_mul_card]; ring

end CommGroup
end Finset

section CommGroup
variable {G : Type*} [CommGroup G] [DecidableEq G] {K L : ℝ} {A B : Finset G} {a : G}

@[to_additive] def IsSmallMul (K : ℝ) (A : Finset G) : Prop := (A * A).card ≤ K * A.card

@[to_additive] def IsSmallDiv (K : ℝ) (A : Finset G) : Prop := (A / A).card ≤ K * A.card

@[to_additive (attr := simp)]
lemma isSmallMul_empty (K : ℝ) : IsSmallMul K (∅ : Finset G) := by simp [IsSmallMul]

@[to_additive (attr := simp)]
lemma isSmallDiv_empty (K : ℝ) : IsSmallDiv K (∅ : Finset G) := by simp [IsSmallDiv]

@[to_additive (attr := simp)]
lemma isSmallMul_singleton : IsSmallMul K {a} ↔ 1 ≤ K := by simp [IsSmallMul]

@[to_additive (attr := simp)]
lemma isSmallDiv_singleton : IsSmallDiv K {a} ↔ 1 ≤ K := by simp [IsSmallDiv]

@[to_additive IsSmallAdd.one_le]
lemma IsSmallMul.one_le (hA : IsSmallMul K A) (hA' : A.Nonempty) : 1 ≤ K := by
  by_contra! hK
  refine lt_irrefl (A.card : ℝ) ?_
  calc
    (A.card : ℝ) ≤ (A * A).card := mod_cast card_le_card_mul_right A hA'
    _ ≤ K * A.card := hA
    _ < A.card := mul_lt_of_lt_one_left (by positivity) hK

@[to_additive IsSmallSub.one_le]
lemma IsSmallDiv.one_le (hA : IsSmallDiv K A) (hA' : A.Nonempty) : 1 ≤ K := by
  by_contra! hK
  refine lt_irrefl (A.card : ℝ) ?_
  calc
    (A.card : ℝ) ≤ (A / A).card := mod_cast card_le_card_div_right hA'
    _ ≤ K * A.card := hA
    _ < A.card := mul_lt_of_lt_one_left (by positivity) hK

@[to_additive] lemma IsSmallMul.pos (hA : IsSmallMul K A) (hA' : A.Nonempty) : 0 < K :=
  zero_lt_one.trans_le $ hA.one_le hA'

@[to_additive] lemma IsSmallDiv.pos (hA : IsSmallDiv K A) (hA' : A.Nonempty) : 0 < K :=
  zero_lt_one.trans_le $ hA.one_le hA'

@[to_additive]
lemma IsSmallMul.mono (hKL : K ≤ L) (hA : IsSmallMul K A) : IsSmallMul L A := hA.trans (by gcongr)

@[to_additive]
lemma IsSmallDiv.mono (hKL : K ≤ L) (hA : IsSmallDiv K A) : IsSmallDiv L A := hA.trans (by gcongr)

/-- If `A` has small difference, then it has small doubling, with the constant squared.

This is a consequence of the Ruzsa triangle inequality. -/
@[to_additive
"If `A` has small difference, then it has small doubling, with the constant squared.

This is a consequence of the Ruzsa triangle inequality."]
lemma IsSmallDiv.isSmallMul (hA : IsSmallDiv K A) : IsSmallMul (K ^ 2) A := by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_right ?_ (Nat.cast_pos.2 hA'.card_pos)
  calc
    (A * A).card * (A.card : ℝ) ≤ (A / A).card * (A / A).card := by
      norm_cast; exact card_mul_mul_le_card_div_mul_card_div _ _ _
    _ ≤ (K * A.card) * (K * A.card) := by have := hA.pos hA'; gcongr <;> exact hA
    _ = K ^ 2 * A.card * A.card := by ring


/-- If `A` has small doubling, then it has small difference, with the constant squared.

This is a consequence of the Ruzsa triangle inequality. -/
@[to_additive
"If `A` has small doubling, then it has small difference, with the constant squared.

This is a consequence of the Ruzsa triangle inequality."]
lemma IsSmallMul.isSmallDiv (hA : IsSmallMul K A) : IsSmallDiv (K ^ 2) A := by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_right ?_ (Nat.cast_pos.2 hA'.card_pos)
  calc
    (A / A).card * (A.card : ℝ) ≤ (A * A).card * (A * A).card := by
      norm_cast; exact card_div_mul_le_card_mul_mul_card_mul A A A
    _ ≤ (K * A.card) * (K * A.card) := by have := hA.pos hA'; gcongr <;> exact hA
    _ = K ^ 2 * A.card * A.card := by ring
