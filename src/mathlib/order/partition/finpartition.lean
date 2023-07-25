import mathlib.data.finset.image
import order.partition.finpartition

open finset function

variables {α β : Type*} [decidable_eq α] [decidable_eq β]

namespace finpartition

@[simps]
def finset_image {a : finset α} (P : finpartition a) (f : α → β) (hf : injective f) :
  finpartition (a.image f) :=
{ parts := P.parts.image (image f),
  sup_indep := begin
    rw [sup_indep_iff_pairwise_disjoint, coe_image,
      (hf.finset_image.inj_on _).pairwise_disjoint_image],
    simp only [set.pairwise_disjoint, set.pairwise, mem_coe, function.on_fun, ne.def,
      function.comp.left_id, disjoint_image hf],
    exact P.disjoint,
  end,
  sup_parts := begin
    ext i,
    simp only [mem_sup, mem_image, exists_prop, id.def, exists_exists_and_eq_and],
    split,
    { rintro ⟨j, hj, i, hij, rfl⟩,
      exact ⟨_, P.le hj hij, rfl⟩ },
    rintro ⟨j, hj, rfl⟩,
    rw ←P.sup_parts at hj,
    simp only [mem_sup, id.def, exists_prop] at hj,
    obtain ⟨b, hb, hb'⟩ := hj,
    exact ⟨b, hb, _, hb', rfl⟩,
  end,
  not_bot_mem := by simpa only [bot_eq_empty, mem_image, image_eq_empty, exists_prop,
    exists_eq_right] using P.not_bot_mem }

def extend' [distrib_lattice α] [order_bot α] {a b c : α} (P : finpartition a) (hab : disjoint a b)
  (hc : a ⊔ b = c) : finpartition c :=
if hb : b = ⊥ then P.copy (by rw [←hc, hb, sup_bot_eq]) else P.extend hb hab hc

def mod_partitions (s d : ℕ) (hd : d ≠ 0) (h : d ≤ s) : finpartition (range s) :=
{ parts := (range d).image (λ i, (range s).filter (λ j, j % d = i)),
  sup_indep :=
  begin
    rw [sup_indep_iff_pairwise_disjoint, coe_image, set.inj_on.pairwise_disjoint_image],
    { simp only [set.pairwise_disjoint, function.on_fun, set.pairwise, mem_coe, mem_range,
        disjoint_left, function.comp.left_id, mem_filter, not_and, and_imp],
      rintro x hx y hy hxy a ha rfl _,
      exact hxy },
    simp only [set.inj_on, coe_range, set.mem_Iio],
    intros x₁ hx₁ x₂ hx₂ h',
    have : x₁ ∈ (range s).filter (λ j, j % d = x₂),
    { rw [←h', mem_filter, mem_range, nat.mod_eq_of_lt hx₁],
      simp only [hx₁.trans_le h, eq_self_iff_true, and_self] },
    rw [mem_filter, nat.mod_eq_of_lt hx₁] at this,
    exact this.2
  end,
  sup_parts :=
  begin
    rw [sup_image, function.comp.left_id],
    refine subset.antisymm _ _,
    { rw [finset.sup_eq_bUnion, bUnion_subset],
      simp only [filter_subset, implies_true_iff] },
    intros i hi,
    have : 0 < d := hd.bot_lt,
    simpa [mem_sup, nat.mod_lt _ this] using hi,
  end,
  not_bot_mem :=
  begin
    simp only [bot_eq_empty, mem_image, mem_range, exists_prop, not_exists, not_and,
      filter_eq_empty_iff, not_forall, not_not],
    intros i hi,
    exact ⟨_, hi.trans_le h, nat.mod_eq_of_lt hi⟩,
  end }

lemma mod_partitions_parts_eq (s d : ℕ) (hd : d ≠ 0) (h : d ≤ s) :
  (mod_partitions s d hd h).parts =
    (range d).image (λ i, (range ((s - i - 1) / d + 1)).image (λ x, i + d * x)) :=
begin
  rw [mod_partitions],
  ext x,
  simp only [mem_image, mem_range],
  refine bex_congr (λ i hi, _),
  suffices : (range ((s - i - 1) / d + 1)).image (λ x, i + d * x) =
    (range s).filter (λ j, j % d = i),
  { rw this },
  clear x,
  ext j,
  simp only [mem_image, mem_filter, mem_range, nat.lt_add_one_iff],
  split,
  { rintro ⟨j, hj, rfl⟩,
    rw [nat.add_mul_mod_self_left, nat.mod_eq_of_lt hi, eq_self_iff_true, and_true,
      ←lt_tsub_iff_left, mul_comm],
    rwa [nat.le_div_iff_mul_le hd.bot_lt, nat.le_sub_iff_right, nat.succ_le_iff] at hj,
    rw [nat.succ_le_iff],
    exact nat.sub_pos_of_lt (hi.trans_le h) },
  { rintro ⟨hj, rfl⟩,
    refine ⟨j / d, _, nat.mod_add_div _ _⟩,
    rwa [nat.le_div_iff_mul_le' hd.bot_lt, le_tsub_iff_right, le_tsub_iff_left, ←add_assoc,
      mul_comm, nat.mod_add_div, nat.add_one_le_iff],
    { exact hi.le.trans h },
    rw [nat.succ_le_iff],
    exact nat.sub_pos_of_lt (hi.trans_le h) }
end

end finpartition
