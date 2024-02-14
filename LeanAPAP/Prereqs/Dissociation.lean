import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Pointwise.Basic
import LeanAPAP.Mathlib.Algebra.BigOperators.Basic

/-!
# Dissociation
-/

open scoped BigOperators Pointwise

variable {α β : Type*} [CommGroup α] [CommGroup β]

section dissociation
variable {s : Set α} {t u : Finset α} {K : ℕ} {a : α}
open Set

@[to_additive]
def MulDissociated (s : Set α) : Prop := {t : Finset α | ↑t ⊆ s}.InjOn (∏ x in ·, x)

@[to_additive] lemma mulDissociated_iff_sum_eq_subsingleton :
    MulDissociated s ↔ ∀ a, {t : Finset α | ↑t ⊆ s ∧ ∏ x in t, x = a}.Subsingleton :=
  ⟨fun hs _ _t ht _u hu ↦ hs ht.1 hu.1 $ ht.2.trans hu.2.symm,
    fun hs _t ht _u hu htu ↦ hs _ ⟨ht, htu⟩ ⟨hu, rfl⟩⟩

@[to_additive] lemma MulDissociated.subset {t : Set α} (hst : s ⊆ t) (ht : MulDissociated t) :
    MulDissociated s := ht.mono fun _ ↦ hst.trans'

@[to_additive (attr := simp)]
lemma mulDissociated_empty : MulDissociated (∅ : Set α) := by
  simp [MulDissociated, subset_empty_iff]

@[to_additive (attr := simp)]
lemma mulDissociated_singleton : MulDissociated ({a} : Set α) ↔ a ≠ 1 := by
  simp [MulDissociated, setOf_or, (Finset.singleton_ne_empty _).symm, -subset_singleton_iff,
    Finset.coe_subset_singleton]

@[to_additive (attr := simp)]
lemma not_mulDissociated :
    ¬ MulDissociated s ↔
      ∃ t : Finset α, ↑t ⊆ s ∧ ∃ u : Finset α, ↑u ⊆ s ∧ t ≠ u ∧ ∏ x in t, x = ∏ x in u, x := by
  simp [MulDissociated, InjOn]; aesop

@[to_additive]
lemma not_mulDissociated_iff_exists_disjoint :
    ¬ MulDissociated s ↔
      ∃ B C : Finset α, ↑B ⊆ s ∧ ↑C ⊆ s ∧ Disjoint B C ∧ B ≠ C ∧ ∏ a in B, a = ∏ a in C, a := by
  classical
  refine not_mulDissociated.trans
    ⟨?_, fun ⟨B, C, hB, hC, _, hBCne, hBCsum⟩ ↦ ⟨B, hB, C, hC, hBCne, hBCsum⟩⟩
  rintro ⟨B, hB, C, hC, hBC, h⟩
  refine ⟨B \ C, C \ B, ?_, ?_, disjoint_sdiff_sdiff, sdiff_ne_sdiff_iff.2 hBC,
    Finset.prod_sdiff_eq_prod_sdiff.2 h⟩ <;> push_cast <;> exact (diff_subset _ _).trans ‹_›

@[to_additive (attr := simp)] lemma MulEquiv.mulDissociated_preimage (e : β ≃* α) :
    MulDissociated (e ⁻¹' s) ↔ MulDissociated s := by
  simp [MulDissociated, InjOn, ← e.finsetCongr.forall_congr_left, ← e.apply_eq_iff_eq,
    (Finset.map_injective _).eq_iff]

@[to_additive (attr := simp)] lemma mulDissociated_inv : MulDissociated s⁻¹ ↔ MulDissociated s :=
  (MulEquiv.inv α).mulDissociated_preimage

end dissociation

namespace Finset
variable [DecidableEq α] [Fintype α] {A B C : Finset α} {a : α} {K : ℕ}

@[to_additive] def mulSpan (A : Finset α) : Finset α :=
  (Fintype.piFinset fun _a ↦ ({-1, 0, 1} : Finset ℤ)).image fun c ↦ ∏ a in A, a ^ c a

@[to_additive (attr := simp)]
lemma mem_mulSpan :
    a ∈ mulSpan A ↔ ∃ c : α → ℤ, (∀ a, c a = -1 ∨ c a = 0 ∨ c a = 1) ∧ ∏ a in A, a ^ c a = a := by
  simp [mulSpan]

--TODO: Fix additivisation
@[simp]
lemma subset_addSpan {α : Type*} [AddCommGroup α] [DecidableEq α] [Fintype α] {A : Finset α} :
    A ⊆ addSpan A := fun a ha ↦
  mem_addSpan.2 ⟨Pi.single a 1, fun b ↦ by obtain rfl | hab := eq_or_ne a b <;> simp [*], by
    simp [Pi.single, Function.update, ite_smul, ha]⟩

@[to_additive existing (attr := simp)]
lemma subset_mulSpan : A ⊆ mulSpan A := fun a ha ↦
  mem_mulSpan.2 ⟨Pi.single a 1, fun b ↦ by obtain rfl | hab := eq_or_ne a b <;> simp [*], by
    simp [Pi.single, Function.update, pow_ite, ha]⟩

--TODO: Fix additivisation
lemma sum_sub_sum_mem_addSpan {α : Type*} [AddCommGroup α] [DecidableEq α] [Fintype α]
    {A B C : Finset α} (hB : B ⊆ A) (hC : C ⊆ A) : ∑ a in B, a - ∑ a in C, a ∈ addSpan A :=
  mem_addSpan.2
    ⟨Set.indicator B 1 - Set.indicator C 1, fun a ↦ by
      by_cases a ∈ B <;> by_cases a ∈ C <;> simp [*], by
      simp [sum_sub_distrib, sub_smul, Set.indicator, ite_smul, inter_eq_right.2, *]⟩

@[to_additive existing]
lemma prod_div_prod_mem_mulSpan (hB : B ⊆ A) (hC : C ⊆ A) :
    (∏ a in B, a) / ∏ a in C, a ∈ mulSpan A :=
  mem_mulSpan.2
    ⟨Set.indicator B 1 - Set.indicator C 1, fun a ↦ by
      by_cases a ∈ B <;> by_cases a ∈ C <;> simp [*], by
      simp [prod_div_distrib, zpow_sub, ←div_eq_mul_inv, Set.indicator, pow_ite, inter_eq_right.2,
        *]⟩

@[to_additive]
lemma diss_mulSpan (hA : ∀ A', A' ⊆ A → MulDissociated (A' : Set α) → A'.card ≤ K) :
    ∃ A', A' ⊆ A ∧ A'.card ≤ K ∧ A ⊆ mulSpan A' := by
  classical
  obtain ⟨A', hA', hA'max⟩ :=
    exists_maximal (A.powerset.filter fun A' : Finset α ↦ MulDissociated (A' : Set α))
      ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, by simp⟩⟩
  simp only [mem_filter, mem_powerset, lt_eq_subset, and_imp] at hA' hA'max
  refine' ⟨A', hA'.1, hA _ hA'.1 hA'.2, fun a ha ↦ _⟩
  by_cases ha' : a ∈ A'
  · exact subset_mulSpan ha'
  obtain ⟨B, C, hB, hC, hBC⟩ := not_mulDissociated_iff_exists_disjoint.1 fun h ↦
    hA'max _ (insert_subset_iff.2 ⟨ha, hA'.1⟩) h $ ssubset_insert ha'
  by_cases haB : a ∈ B
  · have : a = (∏ b in C, b) / ∏ b in B.erase a, b := by
      rw [prod_erase_eq_div haB, hBC.2.2, div_div_self']
    rw [this]
    exact prod_div_prod_mem_mulSpan
      ((subset_insert_iff_of_not_mem $ disjoint_left.1 hBC.1 haB).1 hC) (subset_insert_iff.1 hB)
  rw [coe_subset, subset_insert_iff_of_not_mem haB] at hB
  by_cases haC : a ∈ C
  · have : a = (∏ b in B, b) / ∏ b in C.erase a, b := by
      rw [prod_erase_eq_div haC, hBC.2.2, div_div_self']
    rw [this]
    exact prod_div_prod_mem_mulSpan hB (subset_insert_iff.1 hC)
  · rw [coe_subset, subset_insert_iff_of_not_mem haC] at hC
    cases not_mulDissociated_iff_exists_disjoint.2 ⟨B, C, hB, hC, hBC⟩ hA'.2

end Finset
