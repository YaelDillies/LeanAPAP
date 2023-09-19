import Mathlib.Algebra.IndicatorFunction
import LeanAPAP.Mathlib.Algebra.GroupPower.Basic
import LeanAPAP.Mathlib.Data.Finset.Powerset
import LeanAPAP.Mathlib.Data.Fintype.Basic

/-!
# Dissociation
-/

open scoped BigOperators

namespace Finset
variable {α : Type*} [DecidableEq α] [CommGroup α] {A B C : Finset α} {K : ℕ} {a : α}

@[to_additive]
def MulDissociated (A : Finset α) : Prop :=
  ∀ a n, ((A.powersetLen n).filter λ A' ↦ ∏ x in A', x = a : Set $ Finset α).Subsingleton

@[to_additive (attr := simp)]
lemma mulDissociated_empty : MulDissociated (∅ : Finset α) := by
  simp [MulDissociated, Set.Subsingleton, mem_powersetLen, subset_empty]

@[to_additive (attr := simp)]
lemma mulDissociated_singleton (a : α) : MulDissociated ({a} : Finset α) := by
  simp only [MulDissociated, Set.Subsingleton, mem_powersetLen, eq_comm, coe_filter, and_true_iff,
    Set.mem_sep_iff, mem_coe, subset_singleton_iff, and_imp, forall_eq_or_imp, card_empty,
    true_and_iff, sum_empty, forall_eq, card_singleton, sum_singleton, eq_self_iff_true,
    imp_true_iff, Set.mem_setOf_eq]
  refine' λ b n ↦ ⟨_, _⟩ <;> rintro rfl rfl <;> simp

@[to_additive (attr := simp)]
lemma not_mulDissociated :
    ¬MulDissociated A ↔
      ∃ a n, ((A.powersetLen n).filter λ A' ↦ ∏ x in A', x = a : Set $ Finset α).Nontrivial := by simp [MulDissociated]

@[to_additive]
lemma not_mulDissociated_iff_exists_disjoint :
    ¬ MulDissociated A ↔
      ∃ B, B ⊆ A ∧ ∃ C, C ⊆ A ∧ Disjoint B C ∧ B ≠ C ∧ B.card = C.card ∧
        ∏ a in B, a = ∏ a in C, a := by
  refine' not_mulDissociated.trans ⟨_, _⟩
  · rintro ⟨a, n, B, hB, C, hC, hBC⟩
    simp only [coe_filter, Set.mem_sep_iff, mem_coe, mem_powersetLen] at hB hC
    refine'
      ⟨B \ C, (sdiff_subset _ _).trans hB.1.1, C \ B, (sdiff_subset _ _).trans hC.1.1,
        disjoint_sdiff_sdiff, λ h ↦ hBC _, add_left_injective _ $ card_sdiff_add_card.trans _,
        _⟩
    · rw [←sdiff_union_inter B, h, inter_comm, sdiff_union_inter]
    · simp_rw [hC.1.2, ←hB.1.2, card_sdiff_add_card, union_comm]
    · rw [←div_eq_one, prod_sdiff_div_prod_sdiff, hB.2, hC.2, div_self']
  · rintro ⟨B, hB, C, hC, -, hBCne, hBCcard, hBCsum⟩
    refine' ⟨∏ a in B, a, B.card, B, _, C, _, hBCne⟩ <;> simp [*]

@[to_additive]
lemma mulDissociated_iff_forall_lt_card :
    MulDissociated A ↔
      ∀ (a),
        ∀ n < A.card,
          ((A.powersetLen n).filter λ A' ↦ ∏ x in A', x = a : Set $ Finset α).Subsingleton :=
  forall₂_congr λ a n ↦ by
    obtain hn | rfl | hn := lt_trichotomy n A.card <;> simp [*, Set.Subsingleton]

variable [Fintype α]

@[to_additive]
instance : DecidablePred (MulDissociated : Finset α → Prop) := λ A ↦
  decidable_of_iff'
    (∀ a, ∀ n ∈ range A.card,
        ((A.powersetLen n).filter λ A' ↦ ∏ x in A', x = a : Set $ Finset α).Subsingleton)
    (mulDissociated_iff_forall_lt_card.trans $ by simp_rw [←Finset.mem_range])

@[to_additive]
def mulSpan (A : Finset α) : Finset α :=
  (Fintype.piFinset λ _a ↦ ({-1, 0, 1} : Finset ℤ)).image λ c ↦ ∏ a in A, a ^ c a

@[to_additive (attr := simp)]
lemma mem_mulSpan :
    a ∈ mulSpan A ↔ ∃ c : α → ℤ, (∀ a, c a = -1 ∨ c a = 0 ∨ c a = 1) ∧ ∏ a in A, a ^ c a = a := by
  simp [mulSpan]

--TODO: Fix additivisation
@[simp]
lemma subset_addSpan {α : Type*} [DecidableEq α] [AddCommGroup α] {A : Finset α} [Fintype α] :
    A ⊆ addSpan A := λ a ha ↦
  mem_addSpan.2 ⟨Pi.single a 1, λ b ↦ by obtain rfl | hab := eq_or_ne a b <;> simp [*], by
    simp [Pi.single, Function.update, ite_smul, ha]⟩

@[to_additive existing (attr := simp)]
lemma subset_mulSpan : A ⊆ mulSpan A := λ a ha ↦
  mem_mulSpan.2 ⟨Pi.single a 1, λ b ↦ by obtain rfl | hab := eq_or_ne a b <;> simp [*], by
    simp [Pi.single, Function.update, pow_ite, ha]⟩

--TODO: Fix additivisation
lemma sum_sub_sum_mem_addSpan {α : Type*} [DecidableEq α] [AddCommGroup α] {A B C : Finset α}
    [Fintype α] (hB : B ⊆ A) (hC : C ⊆ A) : ∑ a in B, a - ∑ a in C, a ∈ addSpan A :=
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
lemma diss_mulSpan (hA : ∀ (A') (_ : A' ⊆ A), A'.MulDissociated → A'.card ≤ K) :
    ∃ A', A' ⊆ A ∧ A'.card ≤ K ∧ A ⊆ mulSpan A' := by
  obtain ⟨A', hA', hA'max⟩ :=
    exists_maximal (A.powerset.filter MulDissociated)
      ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, mulDissociated_empty⟩⟩
  simp only [mem_filter, mem_powerset, lt_eq_subset, and_imp] at hA' hA'max
  refine' ⟨A', hA'.1, hA _ hA'.1 hA'.2, λ a ha ↦ _⟩
  by_cases ha' : a ∈ A'
  · exact subset_mulSpan ha'
  obtain ⟨B, hB, C, hC, hBC⟩ :=
    not_mulDissociated_iff_exists_disjoint.1 λ h ↦
      hA'max _ (insert_subset_iff.2 ⟨ha, hA'.1⟩) h $ ssubset_insert ha'
  by_cases haB : a ∈ B
  · have : a = (∏ b in C, b) / ∏ b in B.erase a, b := by
      rw [prod_erase_eq_div haB, hBC.2.2.2, div_div_self']
    rw [this]
    exact
      prod_div_prod_mem_mulSpan ((subset_insert_iff_of_not_mem $ disjoint_left.1 hBC.1 haB).1 hC)
        (subset_insert_iff.1 hB)
  rw [subset_insert_iff_of_not_mem haB] at hB
  by_cases haC : a ∈ C
  · have : a = (∏ b in B, b) / ∏ b in C.erase a, b := by
      rw [prod_erase_eq_div haC, hBC.2.2.2, div_div_self']
    rw [this]
    exact prod_div_prod_mem_mulSpan hB (subset_insert_iff.1 hC)
  · rw [subset_insert_iff_of_not_mem haC] at hC
    cases not_mulDissociated_iff_exists_disjoint.2 ⟨B, hB, C, hC, hBC⟩ hA'.2

end Finset
