import algebra.indicator_function
import mathlib.algebra.group_power.basic
import mathlib.data.finset.powerset

/-!
# Dissociation
-/

instance {α : Type*} [fintype α] [decidable_eq α] {s : set α} [decidable_pred (∈ s)] :
  decidable s.subsingleton :=
decidable_of_iff (∀ a ∈ s, ∀ b ∈ s, a = b) iff.rfl

open_locale big_operators

namespace finset
variables {α : Type*} [decidable_eq α] [comm_group α] {A B C : finset α} {K : ℕ} {a : α}

@[to_additive]
def mul_dissociated (A : finset α) : Prop :=
∀ a n, ((A.powerset_len n).filter $ λ A', ∏ x in A', x = a : set $ finset α).subsingleton

@[simp, to_additive] lemma mul_dissociated_empty : mul_dissociated (∅ : finset α) :=
by simp [mul_dissociated, set.subsingleton, mem_powerset_len, subset_empty]

@[simp, to_additive] lemma mul_dissociated_singleton (a : α) : mul_dissociated ({a} : finset α) :=
begin
  simp only [mul_dissociated, set.subsingleton, mem_powerset_len, eq_comm, coe_filter, and_true,
    set.mem_sep_iff, mem_coe, subset_singleton_iff, and_imp, forall_eq_or_imp, card_empty, true_and,
    sum_empty, forall_eq, card_singleton, sum_singleton, eq_self_iff_true, implies_true_iff],
  refine (λ b n, ⟨_, _⟩); rintro rfl rfl; simp,
end

@[simp, to_additive] lemma not_mul_dissociated :
  ¬ mul_dissociated A ↔ ∃ a n,
    ((A.powerset_len n).filter $ λ A', ∏ x in A', x = a : set $ finset α).nontrivial :=
by simp [mul_dissociated]

@[to_additive]
lemma not_mul_dissociated_iff_exists_disjoint :
  ¬ mul_dissociated A ↔
    ∃ (B ⊆ A) (C ⊆ A), disjoint B C ∧ B ≠ C ∧ B.card = C.card ∧ ∏ a in B, a = ∏ a in C, a :=
begin
  refine not_mul_dissociated.trans ⟨_, _⟩,
  { rintro ⟨a, n, B, hB, C, hC, hBC⟩,
    simp only [coe_filter, set.mem_sep_iff, mem_coe, mem_powerset_len] at hB hC,
    refine ⟨B \ C, (sdiff_subset _ _).trans hB.1.1, C \ B, (sdiff_subset _ _).trans hC.1.1,
      disjoint_sdiff_sdiff, λ h, hBC _, add_left_injective _ $ card_sdiff_add_card.trans _, _⟩,
    { rw [←sdiff_union_inter B, h, inter_comm, sdiff_union_inter] },
    { simp_rw [hC.1.2, ←hB.1.2, card_sdiff_add_card, union_comm] },
    { rw [←div_eq_one, prod_sdiff_div_prod_sdiff, hB.2, hC.2, div_self'] } },
  { rintro ⟨B, hB, C, hC, hBCdisj, hBCne, hBCcard, hBCsum⟩,
    refine ⟨∏ a in B, a, B.card, B, _, C, _, hBCne⟩; simp [*] }
end

@[to_additive]
lemma mul_dissociated_iff_forall_lt_card :
  mul_dissociated A ↔ ∀ a (n < A.card),
    ((A.powerset_len n).filter $ λ A', ∏ x in A', x = a : set $ finset α).subsingleton :=
forall₂_congr $ λ a n, by obtain hn | rfl | hn := lt_trichotomy n A.card; simp [*, set.subsingleton]

variables [fintype α]

@[to_additive]
instance : decidable_pred (mul_dissociated : finset α → Prop) :=
λ A, decidable_of_iff' (∀ a (n ∈ range A.card),
  ((A.powerset_len n).filter $ λ A', ∏ x in A', x = a : set $ finset α).subsingleton)
  (mul_dissociated_iff_forall_lt_card.trans $ by simp_rw ←finset.mem_range)

@[to_additive]
def mul_span (A : finset α) : finset α :=
(fintype.pi_finset $ λ a, ({-1, 0, 1} : finset ℤ)).image (λ c, ∏ a in A, a ^ c a)

@[simp, to_additive] lemma mem_mul_span :
  a ∈ mul_span A ↔ ∃ c : α → ℤ, (∀ a, c a = -1 ∨ c a = 0 ∨ c a = 1) ∧ ∏ a in A, a ^ c a = a :=
by simp [mul_span]

--TODO: Fix additivisation
@[simp] lemma subset_add_span {α : Type*} [decidable_eq α] [add_comm_group α] {A : finset α}
  [fintype α] : A ⊆ add_span A :=
λ a ha, mem_add_span.2 ⟨pi.single a 1, λ b, by obtain rfl | hab := eq_or_ne a b; simp [*],
  by simp [pi.single, function.update, ite_smul, ha]⟩

@[simp, to_additive] lemma subset_mul_span : A ⊆ mul_span A :=
λ a ha, mem_mul_span.2 ⟨pi.single a 1, λ b, by obtain rfl | hab := eq_or_ne a b; simp [*],
  by simp [pi.single, function.update, pow_ite, ha]⟩

--TODO: Fix additivisation
lemma sum_sub_sum_mem_add_span {α : Type*} [decidable_eq α] [add_comm_group α] {A B C : finset α}
  [fintype α] (hB : B ⊆ A) (hC : C ⊆ A) : ∑ a in B, a - ∑ a in C, a ∈ add_span A :=
mem_add_span.2 ⟨set.indicator B 1 - set.indicator C 1, λ a,
  by by_cases a ∈ B; by_cases a ∈ C; simp [*], by simp [sum_sub_distrib, sub_smul, set.indicator,
    ite_smul, (inter_eq_right_iff_subset _ _).2, *]⟩

@[to_additive] lemma prod_div_prod_mem_mul_span (hB : B ⊆ A) (hC : C ⊆ A) :
  (∏ a in B, a) / ∏ a in C, a ∈ mul_span A :=
mem_mul_span.2 ⟨set.indicator B 1 - set.indicator C 1, λ a,
  by by_cases a ∈ B; by_cases a ∈ C; simp [*], by simp [prod_div_distrib, zpow_sub, ←div_eq_mul_inv,
    set.indicator, pow_ite, (inter_eq_right_iff_subset _ _).2, *]⟩

@[to_additive] lemma diss_mul_span (hA : ∀ A' ⊆ A, A'.mul_dissociated → A'.card ≤ K) :
  ∃ A' ⊆ A, A'.card ≤ K ∧ A ⊆ mul_span A' :=
begin
  obtain ⟨A', hA', hA'max⟩ := exists_maximal (A.powerset.filter mul_dissociated)
    ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, mul_dissociated_empty⟩⟩,
  simp only [mem_filter, mem_powerset, lt_eq_subset, and_imp] at hA' hA'max,
  refine ⟨A', hA'.1, hA _ hA'.1 hA'.2, λ a ha, _⟩,
  by_cases ha' : a ∈ A',
  { exact subset_mul_span ha' },
  obtain ⟨ B, hB, C, hC, hBC⟩ := not_mul_dissociated_iff_exists_disjoint.1
    (λ h, hA'max _ (insert_subset.2 ⟨ha, hA'.1⟩) h $ ssubset_insert ha'),
  by_cases haB : a ∈ B,
  { have : a = (∏ b in C, b) / ∏ b in B.erase a, b,
    { rw [prod_erase_eq_div haB, hBC.2.2.2, div_div_self'] },
    rw this,
    exact prod_div_prod_mem_mul_span ((subset_insert_iff_of_not_mem $
      disjoint_left.1 hBC.1 haB).1 hC) (subset_insert_iff.1 hB) },
  rw subset_insert_iff_of_not_mem haB at hB,
  by_cases haC : a ∈ C,
  { have : a = (∏ b in B, b) / ∏ b in C.erase a, b,
    { rw [prod_erase_eq_div haC, hBC.2.2.2, div_div_self'] },
    rw this,
    exact prod_div_prod_mem_mul_span hB (subset_insert_iff.1 hC) },
  { rw subset_insert_iff_of_not_mem haC at hC,
    cases not_mul_dissociated_iff_exists_disjoint.2 ⟨B, hB, C, hC, hBC⟩ hA'.2 }
end

end finset
