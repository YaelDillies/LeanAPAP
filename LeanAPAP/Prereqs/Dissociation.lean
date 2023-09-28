import Mathlib.Algebra.IndicatorFunction
import LeanAPAP.Mathlib.Algebra.BigOperators.Basic
import LeanAPAP.Mathlib.Algebra.GroupPower.Basic
import LeanAPAP.Mathlib.Data.Finset.Basic
import LeanAPAP.Mathlib.Data.Finset.Powerset
import LeanAPAP.Mathlib.Data.Fintype.Basic
import LeanAPAP.Mathlib.Order.Heyting.Basic

/-!
# Dissociation
-/

open scoped BigOperators

variable {α : Type*} [CommGroup α]

namespace Set
variable {s : Set α} {K : ℕ} {a : α}

@[to_additive]
def MulDissociated (s : Set α) : Prop :=
  ∀ a, {A' : Finset α | ↑A' ⊆ s ∧ ∏ x in A', x = a}.Subsingleton

@[to_additive (attr := simp)]
lemma mulDissociated_empty : MulDissociated (∅ : Set α) := by
  simp [MulDissociated, Set.Subsingleton, subset_empty_iff]

@[to_additive (attr := simp)]
lemma mulDissociated_singleton : MulDissociated ({a} : Set α) ↔ a ≠ 1 := by
  simp [MulDissociated, Set.Subsingleton, eq_comm, (Finset.singleton_ne_empty _).symm, forall_and, -subset_singleton_iff, Finset.coe_subset_singleton]

@[to_additive (attr := simp)]
lemma not_mulDissociated :
    ¬ MulDissociated s ↔ ∃ a, {A' : Finset α | ↑A' ⊆ s ∧ ∏ x in A', x = a}.Nontrivial := by
  simp [MulDissociated]

@[to_additive]
lemma not_mulDissociated_iff_exists_disjoint :
    ¬ MulDissociated s ↔
      ∃ B C : Finset α, ↑B ⊆ s ∧ ↑C ⊆ s ∧ Disjoint B C ∧ B ≠ C ∧ ∏ a in B, a = ∏ a in C, a := by
  classical
  refine' not_mulDissociated.trans ⟨_, _⟩
  · rintro ⟨a, B, hB, C, hC, hBC⟩
    refine' ⟨B \ C, C \ B, _, _, disjoint_sdiff_sdiff, sdiff_ne_sdiff.2 hBC,
      Finset.prod_sdiff_eq_prod_sdiff.2 $ by rw [hB.2, hC.2]⟩
      <;> push_cast <;> refine (diff_subset _ _).trans ?_
    exacts [hB.1, hC.1]
  · rintro ⟨B, C, hB, hC, -, hBCne, hBCsum⟩
    refine' ⟨∏ a in B, a, B, _, C, _, hBCne⟩ <;> simp [*]

end Set

namespace Finset
variable [DecidableEq α] [Fintype α] {A B C : Finset α} {a : α} {K : ℕ}

@[to_additive] def mulSpan (A : Finset α) : Finset α :=
  (Fintype.piFinset λ _a ↦ ({-1, 0, 1} : Finset ℤ)).image λ c ↦ ∏ a in A, a ^ c a

@[to_additive (attr := simp)]
lemma mem_mulSpan :
    a ∈ mulSpan A ↔ ∃ c : α → ℤ, (∀ a, c a = -1 ∨ c a = 0 ∨ c a = 1) ∧ ∏ a in A, a ^ c a = a := by
  simp [mulSpan]

--TODO: Fix additivisation
@[simp]
lemma subset_addSpan {α : Type*} [AddCommGroup α] [DecidableEq α] [Fintype α] {A : Finset α} :
    A ⊆ addSpan A := λ a ha ↦
  mem_addSpan.2 ⟨Pi.single a 1, λ b ↦ by obtain rfl | hab := eq_or_ne a b <;> simp [*], by
    simp [Pi.single, Function.update, ite_smul, ha]⟩

@[to_additive existing (attr := simp)]
lemma subset_mulSpan : A ⊆ mulSpan A := λ a ha ↦
  mem_mulSpan.2 ⟨Pi.single a 1, λ b ↦ by obtain rfl | hab := eq_or_ne a b <;> simp [*], by
    simp [Pi.single, Function.update, pow_ite, ha]⟩

--TODO: Fix additivisation
lemma sum_sub_sum_mem_addSpan {α : Type*} [AddCommGroup α] [DecidableEq α] [Fintype α]
    {A B C : Finset α} (hB : B ⊆ A) (hC : C ⊆ A) : ∑ a in B, a - ∑ a in C, a ∈ addSpan A :=
  mem_addSpan.2
    ⟨Set.indicator B 1 - Set.indicator C 1, λ a ↦ by
      by_cases a ∈ B <;> by_cases a ∈ C <;> simp [*], by
      simp [sum_sub_distrib, sub_smul, Set.indicator, ite_smul, (inter_eq_right_iff_subset _ _).2,
        *]⟩

@[to_additive existing]
lemma prod_div_prod_mem_mulSpan (hB : B ⊆ A) (hC : C ⊆ A) :
    (∏ a in B, a) / ∏ a in C, a ∈ mulSpan A :=
  mem_mulSpan.2
    ⟨Set.indicator B 1 - Set.indicator C 1, λ a ↦ by
      by_cases a ∈ B <;> by_cases a ∈ C <;> simp [*], by
      simp [prod_div_distrib, zpow_sub, ←div_eq_mul_inv, Set.indicator, pow_ite,
        (inter_eq_right_iff_subset _ _).2, *]⟩

@[to_additive]
lemma diss_mulSpan (hA : ∀ A', A' ⊆ A → (A' : Set α).MulDissociated → A'.card ≤ K) :
    ∃ A', A' ⊆ A ∧ A'.card ≤ K ∧ A ⊆ mulSpan A' := by
  classical
  obtain ⟨A', hA', hA'max⟩ :=
    exists_maximal (A.powerset.filter λ A' : Finset α ↦ Set.MulDissociated (A' : Set α))
      ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, by simp⟩⟩
  simp only [mem_filter, mem_powerset, lt_eq_subset, and_imp] at hA' hA'max
  refine' ⟨A', hA'.1, hA _ hA'.1 hA'.2, λ a ha ↦ _⟩
  by_cases ha' : a ∈ A'
  · exact subset_mulSpan ha'
  obtain ⟨B, C, hB, hC, hBC⟩ :=
    Set.not_mulDissociated_iff_exists_disjoint.1 λ h ↦
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
    cases Set.not_mulDissociated_iff_exists_disjoint.2 ⟨B, C, hB, hC, hBC⟩ hA'.2

end Finset
