import algebra.big_operators.basic
import mathlib.data.finset.powerset
import prereqs.indicator

/-!
# Dissociation
-/

instance {α : Type*} [fintype α] [decidable_eq α] {s : set α} [decidable_pred (∈ s)] :
  decidable s.subsingleton :=
decidable_of_iff (∀ a ∈ s, ∀ b ∈ s, a = b) iff.rfl

open_locale big_operators

namespace finset
variables {α : Type*} [decidable_eq α] [add_comm_group α] {A B C: finset α} {K : ℕ}
  {a : α}

def dissociated (A : finset α) : Prop :=
∀ a n, ((A.powerset_len n).filter $ λ A', ∑ x in A', x = a : set $ finset α).subsingleton

@[simp] lemma dissociated_empty : dissociated (∅ : finset α) :=
by simp [dissociated, set.subsingleton, mem_powerset_len, subset_empty]

@[simp] lemma dissociated_singleton (a : α) : dissociated ({a} : finset α) :=
begin
  simp only [dissociated, set.subsingleton, mem_powerset_len, eq_comm, coe_filter, set.mem_sep_iff,
    mem_coe, subset_singleton_iff, and_imp, forall_eq_or_imp, card_empty, sum_empty, forall_eq,
    card_singleton, sum_singleton, eq_self_iff_true, implies_true_iff, true_and, and_true],
  refine (λ b n, ⟨_, _⟩); rintro rfl rfl; simp,
end

@[simp] lemma not_dissociated :
  ¬ dissociated A ↔ ∃ a n,
    ((A.powerset_len n).filter $ λ A', ∑ x in A', x = a : set $ finset α).nontrivial :=
by simp [dissociated]

lemma not_dissociated_iff_exists_disjoint :
  ¬ dissociated A ↔
    ∃ (B ⊆ A) (C ⊆ A), disjoint B C ∧ B ≠ C ∧ B.card = C.card ∧ ∑ a in B, a = ∑ a in C, a :=
begin
  refine not_dissociated.trans ⟨_, _⟩,
  { rintro ⟨a, n, B, hB, C, hC, hBC⟩,
    simp only [coe_filter, set.mem_sep_iff, mem_coe, mem_powerset_len] at hB hC,
    refine ⟨B \ C, (sdiff_subset _ _).trans hB.1.1, C \ B, (sdiff_subset _ _).trans hC.1.1,
      disjoint_sdiff_sdiff, λ h, hBC _, add_left_injective _ $ card_sdiff_add_card.trans _, _⟩,
    { rw [←sdiff_union_inter B, h, inter_comm, sdiff_union_inter] },
    { simp_rw [hC.1.2, ←hB.1.2, card_sdiff_add_card, union_comm] },
    { rw [←sub_eq_zero, sum_sdiff_sub_sum_sdiff, hB.2, hC.2, sub_self] } },
  { rintro ⟨B, hB, C, hC, hBCdisj, hBCne, hBCcard, hBCsum⟩,
    refine ⟨∑ a in B, a, B.card, B, _, C, _, hBCne⟩; simp [*] }
end

lemma dissociated_iff_forall_lt_card :
  dissociated A ↔ ∀ a (n < A.card),
    ((A.powerset_len n).filter $ λ A', ∑ x in A', x = a : set $ finset α).subsingleton :=
forall₂_congr $ λ a n, by obtain hn | rfl | hn := lt_trichotomy n A.card; simp [*, set.subsingleton]

variables [fintype α]

instance : decidable_pred (dissociated : finset α → Prop) :=
λ A, decidable_of_iff' (∀ a (n ∈ range A.card),
  ((A.powerset_len n).filter $ λ A', ∑ x in A', x = a : set $ finset α).subsingleton) (dissociated_iff_forall_lt_card.trans $ by simp_rw ←finset.mem_range)

def span (A : finset α) : finset α :=
(fintype.pi_finset $ λ a, ({-1, 0, 1} : finset ℤ)).image (λ c, ∑ a in A, c a • a)

@[simp] lemma mem_span :
  a ∈ span A ↔ ∃ c : α → ℤ, (∀ a, c a = -1 ∨ c a = 0 ∨ c a = 1) ∧ ∑ a in A, c a • a = a :=
by simp [span]

@[simp] lemma subset_span : A ⊆ span A :=
λ a ha, mem_span.2 ⟨pi.single a 1, λ b, by obtain rfl | hab := eq_or_ne a b; simp [*],
  by simp [pi.single, function.update, ite_smul, ha]⟩

lemma sum_subset_sum_mem_span (hB : B ⊆ A) (hC : C ⊆ A) : ∑ a in B, a - ∑ a in C, a ∈ span A :=
mem_span.2 ⟨set.indicator B 1 - set.indicator C 1, λ a, by by_cases a ∈ B; by_cases a ∈ C; simp [*],
  by simp [sum_sub_distrib, sub_smul, set.indicator, ite_smul,
    (inter_eq_right_iff_subset _ _).2, *]⟩

lemma diss_span (hA : ∀ A' ⊆ A, A'.dissociated → A'.card ≤ K) :
  ∃ A' ⊆ A, A'.card ≤ K ∧ A ⊆ span A' :=
begin
  obtain ⟨A', hA', hA'max⟩ := exists_maximal (A.powerset.filter dissociated)
    ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, dissociated_empty⟩⟩,
  simp only [mem_filter, mem_powerset, lt_eq_subset, and_imp] at hA' hA'max,
  refine ⟨A', hA'.1, hA _ hA'.1 hA'.2, λ a ha, _⟩,
  by_cases ha' : a ∈ A',
  { exact subset_span ha' },
  obtain ⟨ B, hB, C, hC, hBC⟩ := not_dissociated_iff_exists_disjoint.1
    (λ h, hA'max _ (insert_subset.2 ⟨ha, hA'.1⟩) h $ ssubset_insert ha'),
  by_cases haB : a ∈ B,
  { have : a = ∑ b in C, b - ∑ b in B.erase a, b,
    { rw [sum_erase_eq_sub haB, hBC.2.2.2, sub_sub_self] },
    rw this,
    exact sum_subset_sum_mem_span ((subset_insert_iff_of_not_mem $
      disjoint_left.1 hBC.1 haB).1 hC) (subset_insert_iff.1 hB) },
  rw subset_insert_iff_of_not_mem haB at hB,
  by_cases haC : a ∈ C,
  { have : a = ∑ b in B, b - ∑ b in C.erase a, b,
    { rw [sum_erase_eq_sub haC, hBC.2.2.2, sub_sub_self] },
    rw this,
    exact sum_subset_sum_mem_span hB (subset_insert_iff.1 hC) },
  { rw subset_insert_iff_of_not_mem haC at hC,
    cases not_dissociated_iff_exists_disjoint.2 ⟨B, hB, C, hC, hBC⟩ hA'.2 }
end

end finset
