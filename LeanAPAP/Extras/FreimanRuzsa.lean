import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Data.Finset.Pointwise
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Rify
import LeanAPAP.Mathlib.Algebra.Group.Subgroup.Basic
import LeanAPAP.Mathlib.Combinatorics.Enumerative.DoubleCounting

open Finset
open scoped Pointwise

attribute [norm_cast] Subgroup.coe_set_mk

variable {G : Type*} [CommGroup G] [DecidableEq G] {K L : ℝ} {A B : Finset G} {a : G}

/-- If `A` has doubling strictly less than `3 / 2`, then it is contained in a subspace of size at
most `3/2 |A|`.

This is a very special case of the Freiman-Ruzsa theorem. -/
theorem IsSmallMul.exists_subgroup_le_three_halves_mul_card (hA : (A * A).card < (3/2 : ℝ) * A.card)
    (hA' : A.Nonempty) :
    ∃ V : Subgroup G, ∃ a : G, Nat.card V < (3 / 2 : ℝ) * A.card ∧ (A : Set G) ⊆ a • V := by
  -- For all `a` and `b`, `a + A` and `b + A` intersect in `> |A| / 2` elements because
  -- `|a + A ∪ b + A| ≤ |A + A| < 3/2 |A|` and so
  -- `|a + A ∩ b + A| = 2|A| - |a + A ∪ b + A| > |A| / 2`.
  have key {a b : G} (ha : a ∈ A) (hb : b ∈ A) : (A.card : ℝ) / 2 < (a • A ∩ b • A).card :=
    calc
      _ = (a • A).card + (b • A).card - (3/2 : ℝ) * A.card := by simp; ring
      _ < (a • A).card + (b • A).card - (A * A).card := by gcongr
      _ ≤ (a • A).card + (b • A).card - (a • A ∪ b • A).card := by
        gcongr; exact union_subset (smul_finset_subset_smul ha) (smul_finset_subset_smul hb)
      _ = (a • A ∩ b • A).card := cast_card_inter.symm
  -- `A - A` is a subgroup since clearly it contains `0` and is closed under negation, and further
  -- if `a, b, c, d ∈ A` then `|A ∩ a - b + A| + |A ∩ d - c + A| > |A|` so `a - b + A` and
  -- `d - c + A` intersect, meaning that `(a - b) + (c - d) ∈ A - A`.
  use
    { carrier := A / A,
      one_mem' := by simp [hA'.ne_empty]
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        obtain ⟨_, ⟨e, he, hef⟩, ⟨f, hf, rfl⟩⟩ : ((a / b) • A ∩ (d / c) • A : Set G).Nonempty := by
          norm_cast
          refine Nonempty.mono (s := ((a / b) • A ∩ A) ∩ ((d / c) • A ∩ A))
            (by gcongr <;> apply inter_subset_left) $ inter_nonempty_of_card_lt_card_add_card
            (inter_subset_right ..) (inter_subset_right ..) ?_
          rw [← card_smul_finset b (_ ∩ _), ← card_smul_finset c (_ ∩ _), smul_finset_inter,
            smul_finset_inter, smul_smul, smul_smul, mul_div_cancel, mul_div_cancel]
          rify
          linarith [key ha hb, key hd hc]
        refine ⟨_, hf, _, he, ?_⟩
        dsimp at hef ⊢
        rwa [mul_comm _ f, ← div_eq_div_iff_mul_eq_mul, div_div_eq_mul_div, eq_comm, mul_div_assoc]
          at hef
      inv_mem' := by rintro _ ⟨a, ha, b, hb, rfl⟩; exact ⟨b, hb, a, ha, by simp⟩ }
  have : (A / A).card / (2 : ℝ) < A.card := by
    refine lt_of_mul_lt_mul_of_nonneg_left ?_ A.card.cast_nonneg
    calc
      _ = (A / A).card • (A.card / 2 : ℝ) := by ring
      _ < (A ×ˢ A).card • 1 :=
        card_nsmul_lt_card_nsmul_of_lt_of_le (fun x (a, b) ↦ x = a / b) (hA'.div hA') ?_ ?_
      _ = A.card * A.card := by simp [sq]
    · simp only [bipartiteAbove, mem_div]
      rintro _ ⟨a, ha, b, hb, rfl⟩
      refine (key ha hb).trans_le ?_
      norm_cast
      refine card_le_card_of_surjOn (fun (c, d) ↦ c * b) ?_
      · simp only [Set.SurjOn, coe_inter, coe_smul_finset, coe_filter, mem_product, Set.subset_def,
          Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq, Prod.exists, and_imp, and_assoc]
        rintro _ ⟨c, hc, hcd⟩ ⟨d, hd, rfl⟩
        dsimp at hcd ⊢
        exact ⟨d, c, hd, hc, by rw [div_eq_div_iff_mul_eq_mul, hcd, mul_comm], mul_comm ..⟩
    · simp (config := { contextual := true }) [bipartiteBelow, card_le_one]
  simp only [Subgroup.mem_mk, Nat.card_eq_fintype_card, ← coe_div, Fintype.card_coe, mem_coe]
  obtain ⟨a, ha⟩ := hA'
  refine ⟨a, ?_, ?_⟩
  · calc
      _ ≤ ((a⁻¹ • A * a⁻¹ • A).card : ℝ) := ?_
      _ = (A * A).card := by simp [smul_mul_assoc, mul_smul_comm]
      _ < 3 / 2 * A.card := hA
    gcongr
    rintro v hv
    sorry
  · norm_cast
    norm_cast -- Strange. Why is `norm_cast` not idempotent?
    rw [← inv_mul_eq_div, subset_smul_finset_iff]
    exact smul_finset_subset_smul (inv_mem_inv ha)
