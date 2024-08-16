import Mathlib

open scoped Pointwise

open Finset MulOpposite

variable {G : Type*} [DecidableEq G] [Group G] {A B : Finset G}

-- Throughout this file I use {x} * A rather than x • A largely because x • A is surprisingly
-- tricky to work with.
-- TODO: (maybe Yaël, who's thought about this a lot already?) make the API for x • A (in both Set
-- and Finset) better.

lemma singleton_mul_eq_smul {a : G} : {a} * A = a • A := singleton_mul _
lemma smul_finset_subset_mul {a : G} : a ∈ A → a • B ⊆ A * B := image_subset_image₂_right

-- This came up a few times, it's useful to get size bounds on xA ∩ yA
lemma big_intersection {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    2 * A.card ≤ ((x • A) ∩ (y • A)).card + (A * A).card := by
  have : ((x • A) ∪ (y • A)).card ≤ (A * A).card := by
    refine card_le_card ?_
    rw [union_subset_iff]
    exact ⟨smul_finset_subset_mul hx, smul_finset_subset_mul hy⟩
  refine (add_le_add_left this _).trans_eq' ?_
  rw [card_inter_add_card_union]
  simp only [card_smul_finset, two_mul]

lemma mul_comm_of_doubling_aux (h : (A * A).card < 2 * A.card) : A⁻¹ * A ⊆ A * A⁻¹ := by
  intro z
  simp only [mem_mul, forall_exists_index, exists_and_left, and_imp, mem_inv,
    exists_exists_and_eq_and]
  rintro x hx y hy rfl
  have ⟨t, ht⟩ : ((x • A) ∩ (y • A)).Nonempty := by
    rw [←card_pos]
    linarith [big_intersection hx hy]
  simp only [mem_inter, mem_smul_finset, smul_eq_mul] at ht
  obtain ⟨⟨z, hz, hzxwy⟩, w, hw, rfl⟩ := ht
  refine ⟨z, hz, w, hw, ?_⟩
  rw [mul_inv_eq_iff_eq_mul, mul_assoc, ←hzxwy, inv_mul_cancel_left]

-- TODO: is there a way to get wlog to make `mul_comm_of_doubling_aux` a goal?
-- ie wlog in the target rather than hypothesis
-- (BM: third time seeing this pattern)
-- I'm thinking something like wlog_suffices, where I could write
-- wlog_suffices : A⁻¹ * A ⊆ A * A⁻¹
-- which reverts *everything* (just like wlog does) and makes the side goal A⁻¹ * A = A * A⁻¹
-- under the assumption A⁻¹ * A ⊆ A * A⁻¹
-- and changes the main goal to A⁻¹ * A ⊆ A * A⁻¹
lemma mul_comm_of_doubling (h : (A * A).card < 2 * A.card) :
    A * A⁻¹ = A⁻¹ * A := by
  refine Finset.Subset.antisymm ?_ (mul_comm_of_doubling_aux h)
  have : A⁻¹⁻¹ * A⁻¹ ⊆ A⁻¹ * A⁻¹⁻¹ := by
    refine mul_comm_of_doubling_aux ?_
    simpa only [card_inv, ←mul_inv_rev]
  rwa [inv_inv] at this

lemma coe_mul_comm_of_doubling (h : (A * A).card < 2 * A.card) :
    (A * A⁻¹ : Set G) = A⁻¹ * A := by
  rw [←Finset.coe_mul, mul_comm_of_doubling h, Finset.coe_mul]

lemma weaken_doubling (h : (A * A).card < (3 / 2 : ℚ) * A.card) :
    (A * A).card < 2 * A.card := by
  rw [←Nat.cast_lt (α := ℚ), Nat.cast_mul, Nat.cast_two]
  linarith only [h]

lemma nonempty_of_doubling (h : (A * A).card < (3 / 2 : ℚ) * A.card) :
    A.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  simp at h

example {a b c : G} : (a * b) * (b⁻¹ * c) = a * c := by
  simp [mul_assoc]
  -- MulAction.injective a

/--
TODO: better docstring
The subgroup of G that we will show covers a translate of A while not being a lot bigger than
it. While this is clearly a symmetric set that contains 1, showing it's closed under multiplication
uses the doubling hypothesis heavily.
I'm pretty sure 3/2 is sharp for A⁻¹A to be a subgroup?
-/
@[simps]
def symmetricSubgroup (A : Finset G) (h : (A * A).card < (3 / 2 : ℚ) * A.card) : Subgroup G where
  carrier := A⁻¹ * A
  one_mem' := by
    have ⟨x, hx⟩ : A.Nonempty := nonempty_of_doubling h
    exact ⟨x⁻¹, inv_mem_inv hx, x, by simp [hx]⟩
  inv_mem' := by
    intro x
    simp only [Set.mem_mul, Set.mem_inv, coe_inv, forall_exists_index, exists_and_left, mem_coe,
      and_imp]
    rintro a ha b hb rfl
    exact ⟨b⁻¹, by simpa using hb, a⁻¹, ha, by simp⟩
  mul_mem' := by
    have h₁ : ∀ x ∈ A, ∀ y ∈ A, (1 / 2 : ℚ) * A.card < (x • A ∩ y • A).card := by
      intro x hx y hy
      have := big_intersection hx hy
      rw [←Nat.cast_le (α := ℚ), Nat.cast_mul, Nat.cast_add, Nat.cast_two] at this
      linarith
    intro a c ha hc
    simp only [Set.mem_mul, Set.mem_inv, coe_inv, mem_coe, exists_and_left] at ha hc
    obtain ⟨a, ha, b, hb, rfl⟩ := ha
    obtain ⟨c, hc, d, hd, rfl⟩ := hc
    have h₂ : (1 / 2 : ℚ) * A.card < (A ∩ (a * b)⁻¹ • A).card := by
      refine (h₁ b hb _ ha).trans_le ?_
      rw [←card_smul_finset b⁻¹]
      simp [smul_smul, smul_finset_inter]
    have h₃ : (1 / 2 : ℚ) * A.card < (A ∩ (c * d) • A).card := by
      refine (h₁ _ hc d hd).trans_le ?_
      rw [←card_smul_finset c]
      simp [smul_smul, smul_finset_inter]
    have ⟨t, ht⟩ : ((A ∩ (c * d) • A) ∩ (A ∩ (a * b)⁻¹ • A)).Nonempty := by
      rw [←Finset.card_pos, ←Nat.cast_pos (α := ℚ)]
      have := card_inter_add_card_union (A ∩ (c * d) • A) (A ∩ (a * b)⁻¹ • A)
      rw [←Nat.cast_inj (R := ℚ), Nat.cast_add, Nat.cast_add] at this
      have : (((A ∩ (c * d) • A) ∪ (A ∩ (a * b)⁻¹ • A)).card : ℚ) ≤ A.card := by
        rw [Nat.cast_le, ← inter_union_distrib_left]
        exact card_le_card inter_subset_left
      linarith
    simp only [inter_inter_inter_comm, inter_self, mem_inter, ←inv_smul_mem_iff, inv_inv,
      smul_eq_mul, mul_assoc, mul_inv_rev] at ht
    rw [←coe_mul_comm_of_doubling (weaken_doubling h)]
    exact ⟨a * b * t, by simp [ht, mul_assoc], ((c * d)⁻¹ * t)⁻¹, by simp [ht, mul_assoc]⟩

lemma two_two_two (h : (A * A).card < (3 / 2 : ℚ) * A.card) :
    ∃ H : Subgroup G, (H : Set G) = A⁻¹ * A :=
  ⟨symmetricSubgroup _ h, rfl⟩

lemma weak_symmetricSubgroup_bound (h : (A * A).card < (3 / 2 : ℚ) * A.card) :
    (A⁻¹ * A).card < 2 * A.card := by
  have h₀ : A.Nonempty := nonempty_of_doubling h
  have h₁ : ∀ x ∈ A, ∀ y ∈ A, (1 / 2 : ℚ) * A.card < ((x • A) ∩ (y • A)).card := by
    intro x hx y hy
    have := big_intersection hx hy
    rw [←Nat.cast_le (α := ℚ), Nat.cast_mul, Nat.cast_add, Nat.cast_two] at this
    linarith
  have h₂ : ∀ a ∈ A⁻¹ * A,
      (1 / 2 : ℚ) * A.card < ((A ×ˢ A).filter (fun ⟨x, y⟩ => x * y⁻¹ = a)).card := by
    simp only [mem_mul, mem_product, Prod.forall, and_imp, mem_inv, exists_exists_and_eq_and,
      forall_exists_index]
    rintro _ a ha b hb rfl
    refine (h₁ a ha b hb).trans_le ?_
    rw [Nat.cast_le]
    refine card_le_card_of_injOn (fun t => (a⁻¹ * t, b⁻¹ * t)) ?_ (by simp [Set.InjOn])
    simp only [mem_inter, mem_product, and_imp, Prod.forall, mem_filter, mul_inv_rev, inv_inv,
      exists_and_left, exists_eq_left, forall_exists_index, smul_eq_mul,
      forall_apply_eq_imp_iff₂, inv_mul_cancel_left, inv_mul_cancel_right, mem_smul_finset]
    rintro c hc d hd h
    rw [mul_assoc, mul_inv_cancel_left, ← h, inv_mul_cancel_left]
    simp [hd, hc]
  have h₃ : ∀ x ∈ A ×ˢ A, (fun ⟨x, y⟩ => x * y⁻¹) x ∈ A⁻¹ * A := by
    rw [←mul_comm_of_doubling (weaken_doubling h)]
    simp only [mem_product, Prod.forall, mem_mul, and_imp, mem_inv]
    intro a b ha hb
    exact ⟨a, ha, b⁻¹, by simp [hb], rfl⟩
  have : ((1 / 2 : ℚ) * A.card) * (A⁻¹ * A).card < (A.card : ℚ) ^ 2 := by
    rw [←Nat.cast_pow, sq, ←card_product, card_eq_sum_card_fiberwise h₃, Nat.cast_sum]
    refine (Finset.sum_lt_sum_of_nonempty (by simp [h₀]) h₂).trans_eq' ?_
    simp only [sum_const, nsmul_eq_mul, mul_comm]
  have : (0 : ℚ) < A.card := by simpa [card_pos]
  rw [←Nat.cast_lt (α := ℚ), Nat.cast_mul, Nat.cast_two]
  -- passing between ℕ- and ℚ-inequalities is annoying, here and above
  nlinarith

lemma A_subset_aH (a : G) (ha : a ∈ A) : A ⊆ a • (A⁻¹ * A) := by
  rw [←smul_mul_assoc]
  exact subset_mul_right _ (by simp [←inv_smul_mem_iff, inv_mem_inv ha])

lemma subgroup_strong_bound_left (h : (A * A).card < (3 / 2 : ℚ) * A.card) (a : G) (ha : a ∈ A) :
    A * A ⊆ a • op a • (A⁻¹ * A) := by
  have h₁ : (A⁻¹ * A) * (A⁻¹ * A) = A⁻¹ * A := by
    rw [←Finset.coe_inj, coe_mul, coe_mul, ←symmetricSubgroup_coe _ h, coe_mul_coe]
  have h₂ : a • op a • (A⁻¹ * A) = (a • (A⁻¹ * A)) * (op a • (A⁻¹ * A)) := by
    rw [mul_smul_comm, smul_mul_assoc, h₁, smul_comm]
  rw [h₂]
  refine mul_subset_mul (A_subset_aH a ha) ?_
  rw [←mul_comm_of_doubling (weaken_doubling h), ←mul_smul_comm]
  exact subset_mul_left _ (by simp [←inv_smul_mem_iff, inv_mem_inv ha])

lemma subgroup_strong_bound_right (h : (A * A).card < (3 / 2 : ℚ) * A.card) (a : G) (ha : a ∈ A) :
    a • op a • (A⁻¹ * A) ⊆ A * A := by
  intro z hz
  obtain ⟨H, hH⟩ := two_two_two h
  simp only [mem_smul_finset, smul_eq_mul_unop, unop_op, smul_eq_mul, mem_mul, mem_inv,
    exists_exists_and_eq_and, exists_and_left] at hz
  obtain ⟨d, ⟨b, hb, c, hc, rfl⟩, hz⟩ := hz
  let l : Finset G := A ∩ ((z * a⁻¹) • (A⁻¹ * A))
    -- ^ set of x ∈ A st ∃ y ∈ H a with x y = z
  let r : Finset G := (a • (A⁻¹ * A)) ∩ (z • A⁻¹)
    -- ^ set of x ∈ a H st ∃ y ∈ A with x y = z
  have : (A⁻¹ * A) * (A⁻¹ * A) = A⁻¹ * A := by
    rw [←Finset.coe_inj, coe_mul, coe_mul, ←hH, coe_mul_coe]
  have hl : l = A := by
    rw [inter_eq_left, ←this, subset_smul_finset_iff]
    simp only [←hz, mul_inv_rev, inv_inv, ←mul_assoc]
    refine smul_finset_subset_mul ?_
    simp [mul_mem_mul, mem_inv, ha, hb, hc]
  have hr : r = z • A⁻¹ := by
    rw [inter_eq_right, ←this, mul_assoc _ A, ←mul_comm_of_doubling (weaken_doubling h),
      subset_smul_finset_iff]
    simp only [←mul_assoc, smul_smul]
    refine smul_finset_subset_mul ?_
    simp [←hz, mul_mem_mul, ha, hb, hc, mem_inv]
  have lr : l ∪ r ⊆ a • (A⁻¹ * A) := by
    rw [union_subset_iff, hl]
    exact ⟨A_subset_aH a ha, inter_subset_left⟩
  have : l.card = A.card := by rw [hl]
  have : r.card = A.card := by rw [hr, card_smul_finset, card_inv]
  have : (l ∪ r).card < 2 * A.card := by
    refine (card_le_card lr).trans_lt ?_
    rw [card_smul_finset]
    exact weak_symmetricSubgroup_bound h
  have ⟨t, ht⟩ : (l ∩ r).Nonempty := by
    rw [←card_pos]
    linarith [card_inter_add_card_union l r]
  simp only [hl, hr, mem_inter, ←inv_smul_mem_iff, smul_eq_mul, Finset.mem_inv', mul_inv_rev,
    inv_inv] at ht
  rw [mem_mul]
  exact ⟨t, ht.1, t⁻¹ * z, ht.2, by simp⟩

lemma subgroup_strong_bound_equality (h : (A * A).card < (3 / 2 : ℚ) * A.card)
    (a : G) (ha : a ∈ A) :
    a • op a • (A⁻¹ * A) = A * A :=
  (subgroup_strong_bound_right h a ha).antisymm (subgroup_strong_bound_left h a ha)

lemma subgroup_strong_bound (h : (A * A).card < (3 / 2 : ℚ) * A.card) :
    (A⁻¹ * A).card = (A * A).card := by
  obtain ⟨a, ha⟩ := nonempty_of_doubling h
  rw [←subgroup_strong_bound_equality h a ha, card_smul_finset, card_smul_finset]

theorem very_small_doubling (A : Finset G) (h : (A * A).card < (3 / 2 : ℚ) * A.card) :
    ∃ (H : Subgroup G), ∃ a ∈ A,
      (H : Set G).ncard < (3 / 2 : ℚ) * A.card ∧
      (A : Set G) ⊆ a • (H : Set G) := by
  have ⟨a, ha⟩ := nonempty_of_doubling h
  refine ⟨symmetricSubgroup _ h, a, ha, ?_, ?_⟩
  · rwa [symmetricSubgroup_coe, ←coe_mul, Set.ncard_coe_Finset, subgroup_strong_bound h]
  · rw [symmetricSubgroup_coe]
    exact_mod_cast A_subset_aH a ha

-- a A⁻¹ A a⁻¹ ⊆ A⁻¹ A ?

-- lemma very_small_doubling_normalizer (h : (A * A).card < (3 / 2 : ℚ) * A.card)
--     (a : G) (ha : a ∈ A) :
--     {a} * (A⁻¹ * A) = (A⁻¹ * A) * {a} := by
--   suffices : {a} * (A⁻¹ * A) * {a⁻¹} = A⁻¹ * A
--   ·
