import LeanAPAP.Mathlib.Algebra.Order.Field.Basic
import LeanAPAP.Mathlib.Tactic.Positivity.Finset

/-!
# Density of a finite set

This defines the density of a `Finset` and provides induction principles for finsets.

## Main declarations

* `Finsedens t`: `dens s : ℕ` returns the density of `s : Finset α`.

## Notation

If you need to specify the field the density is valued in, `dens[𝕜] s` is notation for
`(dens s : 𝕜)`. Note that no dot notation is allowed.
-/

open Function Multiset Nat

variable {𝕜 α β : Type*}[Fintype α]

namespace Finset
section Semifield
variable [Semifield 𝕜]  {s t : Finset α} {a b : α}

/-- `dens s` is the number of elements of `s`, aka its density. -/
def dens (s : Finset α) : 𝕜 := s.card / Fintype.card α

notation "dens[" 𝕜 "]" => @dens 𝕜

lemma card_div_card_eq_dens (s : Finset α) : dens[𝕜] s = s.card / Fintype.card α := rfl

@[simp] lemma dens_empty : dens[𝕜] (∅ : Finset α) = 0 := by simp [dens]

@[simp] lemma dens_singleton (a : α) : dens ({a} : Finset α) = (Fintype.card α : 𝕜)⁻¹ := by
  simp [dens]

@[simp]
lemma dens_cons (h : a ∉ s) : (s.cons a h).dens = dens s + (Fintype.card α : 𝕜)⁻¹ := by
  simp [dens, add_div]

section CharZero
variable [CharZero 𝕜] [Nonempty α]

@[simp] lemma dens_univ : dens[𝕜] (univ : Finset α) = 1 := by simp [dens, card_univ]

@[simp] lemma dens_eq_zero : dens[𝕜] s = 0 ↔ s = ∅ := by simp [dens]

lemma dens_ne_zero : dens[𝕜] s ≠ 0 ↔ s.Nonempty :=
  dens_eq_zero.not.trans nonempty_iff_ne_empty.symm

protected alias ⟨_, Nonempty.dens_ne_zero⟩ := dens_ne_zero

@[simp] lemma dens_eq_one : dens[𝕜] s = 1 ↔ s = univ := by
  simp [dens, div_eq_one_iff_eq, card_eq_iff_eq_univ]

lemma dens_ne_one : dens[𝕜] s ≠ 1 ↔ s ≠ univ := dens_eq_one.not

end CharZero

end Semifield

section LinearOrderedSemifield
variable [LinearOrderedSemifield 𝕜] {s t : Finset α} {a b : α}

lemma dens_le_dens (h : s ⊆ t) : dens[𝕜] s ≤ dens t :=
  div_le_div_of_nonneg_right (mod_cast card_mono h) $ by positivity

#exit
@[mono]
lemma dens_mono : Monotone (@dens α) := by apply dens_le_of_subset

lemma dens_pos : 0 < dens s ↔ s.Nonempty :=
  pos_iff_ne_zero.trans <| (not_congr dens_eq_zero).trans nonempty_iff_ne_empty.symm

alias ⟨_, Nonempty.dens_pos⟩ := dens_pos

section InsertErase

variable [DecidableEq α]

@[simp]
lemma dens_insert_of_not_mem (h : a ∉ s) : (insert a s).dens = dens s + 1 := by
  rw [← cons_eq_insert _ _ h, dens_cons]

lemma dens_insert_of_mem (h : a ∈ s) : dens (insert a s) = dens s := by rw [insert_eq_of_mem h]

lemma dens_insert_le (a : α) (s : Finset α) : dens (insert a s) ≤ dens s + 1 := by
  by_cases h : a ∈ s
  · rw [insert_eq_of_mem h]
    exact Nat.le_succ _
  · rw [dens_insert_of_not_mem h]

/-- If `a ∈ s` is known, see also `Finsedens t_insert_of_mem` and `Finsedens t_insert_of_not_mem`.
-/
lemma dens_insert_eq_ite : dens (insert a s) = if a ∈ s then dens s else dens s + 1 := by
  by_cases h : a ∈ s
  · rw [dens_insert_of_mem h, if_pos h]
  · rw [dens_insert_of_not_mem h, if_neg h]

@[simp]
lemma dens_doubleton (h : a ≠ b) : ({a, b} : Finset α).dens = 2 := by
  rw [dens_insert_of_not_mem (not_mem_singleton.2 h), dens_singleton]

/-- $\#(s \setminus \{a\}) = \#s - 1$ if $a \in s$. -/
@[simp]
lemma dens_erase_of_mem : a ∈ s → (s.erase a).dens = dens s - 1 :=
  Multisedens t_erase_of_mem

/-- $\#(s \setminus \{a\}) = \#s - 1$ if $a \in s$.
  This result is casted to any additive group with 1,
  so that we don't have to work with `ℕ`-subtraction. -/
@[simp]
lemma cast_dens_erase_of_mem {R} [AddGroupWithOne R] {s : Finset α} (hs : a ∈ s) :
    ((s.erase a).dens : R) = dens s - 1 := by
  rw [dens_erase_of_mem hs, Nat.cast_sub, Nat.cast_one]
  rw [Nat.add_one_le_iff, Finsedens t_pos]
  exact ⟨a, hs⟩

@[simp]
lemma dens_erase_add_one : a ∈ s → (s.erase a).dens + 1 = dens s :=
  Multisedens t_erase_add_one

lemma dens_erase_lt_of_mem : a ∈ s → (s.erase a).dens < dens s :=
  Multisedens t_erase_lt_of_mem

lemma dens_erase_le : (s.erase a).dens ≤ dens s :=
  Multisedens t_erase_le

lemma pred_dens_le_dens_erase : dens s - 1 ≤ (s.erase a).dens := by
  by_cases h : a ∈ s
  · exact (dens_erase_of_mem h).ge
  · rw [erase_eq_of_not_mem h]
    exact Nat.sub_le _ _

/-- If `a ∈ s` is known, see also `Finsedens t_erase_of_mem` and `Finset.erase_eq_of_not_mem`. -/
lemma dens_erase_eq_ite : (s.erase a).dens = if a ∈ s then dens s - 1 else dens s :=
  Multisedens t_erase_eq_ite

end InsertErase

@[simp]
lemma dens_range (n : ℕ) : (range n).dens = n :=
  Multisedens t_range n

@[simp]
lemma dens_attach : s.attach.dens = dens s :=
  Multisedens t_attach

end Finset

section ToMLListultiset

variable [DecidableEq α] (m : Multiset α) (l : List α)

lemma Multisedens t_toFinset : m.toFinsedens t = Multisedens t m.dedup :=
  rfl

lemma Multiset.toFinset_dens_le : m.toFinsedens t ≤ Multisedens t m :=
  dens_le_of_le <| dedup_le _

lemma Multiset.toFinset_dens_of_nodup {m : Multiset α} (h : m.Nodup) :
    m.toFinsedens t = Multisedens t m :=
  congr_arg dens <| Multiset.dedup_eq_self.mpr h

lemma Multiset.dedup_dens_eq_dens_iff_nodup {m : Multiset α} :
    dens m.dedup = dens m ↔ m.Nodup :=
  .trans ⟨fun h ↦ eq_of_le_of_dens_le (dedup_le m) h.ge, congr_arg _⟩ dedup_eq_self

lemma Multiset.toFinset_dens_eq_dens_iff_nodup {m : Multiset α} :
    m.toFinsedens t = dens m ↔ m.Nodup := dedup_dens_eq_dens_iff_nodup

lemma Lisdens t_toFinset : l.toFinsedens t = l.dedup.length :=
  rfl

lemma List.toFinset_dens_le : l.toFinsedens t ≤ l.length :=
  Multiset.toFinset_dens_le ⟦l⟧

lemma List.toFinset_dens_of_nodup {l : List α} (h : l.Nodup) : l.toFinsedens t = l.length :=
  Multiset.toFinset_dens_of_nodup h

end ToMLListultiset

namespace Finset

variable {s t : Finset α} {f : α → β} {n : ℕ}

@[simp]
lemma length_toList (s : Finset α) : s.toList.length = dens s := by
  rw [toList, ← Multiset.coe_dens, Multiset.coe_toList, dens_def]

lemma dens_image_le [DecidableEq β] : (s.image f).dens ≤ dens s := by
  simpa only [dens_map] using (s.1.map f).toFinset_dens_le

lemma dens_image_of_injOn [DecidableEq β] (H : Set.InjOn f s) : (s.image f).dens = dens s := by
  simp only [dens, image_val_of_injOn H, dens_map]

lemma injOn_of_dens_image_eq [DecidableEq β] (H : (s.image f).dens = dens s) : Set.InjOn f s := by
  rw [dens_def, dens_def, image, toFinset] at H
  dsimp only at H
  have : (s.1.map f).dedup = s.1.map f := by
    refine Multiset.eq_of_le_of_dens_le (Multiset.dedup_le _) ?_
    simp only [H, Multisedens t_map, le_rfl]
  rw [Multiset.dedup_eq_self] at this
  exact inj_on_of_nodup_map this

lemma dens_image_iff [DecidableEq β] : (s.image f).dens = dens s ↔ Set.InjOn f s :=
  ⟨injOn_of_dens_image_eq, dens_image_of_injOn⟩

lemma dens_image_of_injective [DecidableEq β] (s : Finset α) (H : Injective f) :
    (s.image f).dens = dens s :=
  dens_image_of_injOn fun _ _ _ _ h => H h

lemma fiber_dens_ne_zero_iff_mem_image (s : Finset α) (f : α → β) [DecidableEq β] (y : β) :
    (s.filter fun x => f x = y).dens ≠ 0 ↔ y ∈ s.image f := by
  rw [← pos_iff_ne_zero, dens_pos, fiber_nonempty_iff_mem_image]

@[simp]
lemma dens_map (f : α ↪ β) : (s.map f).dens = dens s :=
  Multisedens t_map _ _

@[simp]
lemma dens_subtype (p : α → Prop) [DecidablePred p] (s : Finset α) :
    (s.subtype p).dens = (s.filter p).dens := by simp [Finset.subtype]

lemma dens_filter_le (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).dens ≤ dens s :=
  dens_le_of_subset <| filter_subset _ _

lemma eq_of_subset_of_dens_le {s t : Finset α} (h : s ⊆ t) (h₂ : dens t ≤ dens s) : s = t :=
  eq_of_veq <| Multiset.eq_of_le_of_dens_le (val_le_iff.mpr h) h₂

lemma eq_of_superset_of_dens_ge (hst : s ⊆ t) (hts : dens t ≤ dens s) : t = s :=
  (eq_of_subset_of_dens_le hst hts).symm

lemma subset_iff_eq_of_dens_le (h : dens t ≤ dens s) : s ⊆ t ↔ s = t :=
  ⟨fun hst => eq_of_subset_of_dens_le hst h, Eq.subset'⟩

lemma map_eq_of_subset {f : α ↪ α} (hs : s.map f ⊆ s) : s.map f = s :=
  eq_of_subset_of_dens_le hs (dens_map _).ge

lemma filter_dens_eq {p : α → Prop} [DecidablePred p] (h : (s.filter p).dens = dens s) (x : α)
    (hx : x ∈ s) : p x := by
  rw [← eq_of_subset_of_dens_le (s.filter_subset p) h.ge, mem_filter] at hx
  exact hx.2

lemma dens_lt_dens (h : s ⊂ t) : dens s < dens t :=
  dens_lt_of_lt <| val_lt_iff.2 h

lemma dens_eq_of_bijective (f : ∀ i, i < n → α) (hf : ∀ a ∈ s, ∃ i, ∃ h : i < n, f i h = a)
    (hf' : ∀ (i) (h : i < n), f i h ∈ s)
    (f_inj : ∀ (i j) (hi : i < n) (hj : j < n), f i hi = f j hj → i = j) : dens s = n := by
  classical
    have : ∀ a : α, a ∈ s ↔ ∃ (i : _) (hi : i ∈ range n), f i (mem_range.1 hi) = a := fun a =>
      ⟨fun ha =>
        let ⟨i, hi, eq⟩ := hf a ha
        ⟨i, mem_range.2 hi, eq⟩,
        fun ⟨i, hi, eq⟩ => eq ▸ hf' i (mem_range.1 hi)⟩
    have : s = (range n).attach.image fun i => f i.1 (mem_range.1 i.2) := by
      simpa only [ext_iff, mem_image, exists_prop, Subtype.exists, mem_attach, true_and_iff]
    calc
      dens s = dens ((range n).attach.image fun i => f i.1 (mem_range.1 i.2)) := by rw [this]
      _ = dens (range n).attach :=
        (dens_image_of_injective _) fun ⟨i, hi⟩ ⟨j, hj⟩ eq =>
          Subtype.eq <| f_inj i j (mem_range.1 hi) (mem_range.1 hj) eq
      _ = dens (range n) := dens_attach
      _ = n := dens_range n

lemma dens_congr {t : Finset β} (f : ∀ a ∈ s, β) (h₁ : ∀ a ha, f a ha ∈ t)
    (h₂ : ∀ a b ha hb, f a ha = f b hb → a = b) (h₃ : ∀ b ∈ t, ∃ a ha, f a ha = b) :
    dens s = dens t := by
  classical calc
      dens s = s.attach.dens := dens_attach.symm
      _ = (s.attach.image fun a : { a // a ∈ s } => f a.1 a.2).dens :=
        Eq.symm ((dens_image_of_injective _) fun a b h => Subtype.eq <| h₂ _ _ _ _ h)
      _ = dens t :=
        congr_arg dens
          (Finset.ext fun b =>
            ⟨fun h =>
              let ⟨a, _, ha₂⟩ := mem_image.1 h
              ha₂ ▸ h₁ _ _,
              fun h =>
              let ⟨a, ha₁, ha₂⟩ := h₃ b h
              mem_image.2 ⟨⟨a, ha₁⟩, by simp [ha₂]⟩⟩)

lemma dens_le_dens_of_inj_on {t : Finset β} (f : α → β) (hf : ∀ a ∈ s, f a ∈ t)
    (f_inj : ∀ a₁ ∈ s, ∀ a₂ ∈ s, f a₁ = f a₂ → a₁ = a₂) : dens s ≤ dens t := by
  classical calc
      dens s = (s.image f).dens := (dens_image_of_injOn f_inj).symm
      _ ≤ dens t := dens_le_of_subset <| image_subset_iff.2 hf

/-- If there are more pigeons than pigeonholes, then there are two pigeons in the same pigeonhole.
-/
lemma exists_ne_map_eq_of_dens_lt_of_maps_to {t : Finset β} (hc : dens t < dens s) {f : α → β}
    (hf : ∀ a ∈ s, f a ∈ t) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  classical
    by_contra! hz
    refine' hc.not_le (dens_le_dens_of_inj_on f hf _)
    intro x hx y hy
    contrapose
    exact hz x hx y hy

lemma le_dens_of_inj_on_range (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
    (f_inj : ∀ i < n, ∀ j < n, f i = f j → i = j) : n ≤ dens s :=
  calc
    n = dens (range n) := (dens_range n).symm
    _ ≤ dens s := dens_le_dens_of_inj_on f (by simpa only [mem_range] ) (by simpa only [mem_range] )

lemma surj_on_of_inj_on_of_dens_le {t : Finset β} (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : dens t ≤ dens s) :
    ∀ b ∈ t, ∃ a ha, b = f a ha := by
  classical
    intro b hb
    have h : (s.attach.image fun a : { a // a ∈ s } => f a a.prop).dens = dens s :=
      @dens_attach _ s ▸
        dens_image_of_injective _ fun ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ h => Subtype.eq <| hinj _ _ _ _ h
    have h' : image (fun a : { a // a ∈ s } => f a a.prop) s.attach = t :=
      eq_of_subset_of_dens_le
        (fun b h =>
          let ⟨a, _, ha₂⟩ := mem_image.1 h
          ha₂ ▸ hf _ _)
        (by simp [hst, h])
    rw [← h'] at hb
    obtain ⟨a, _, ha₂⟩ := mem_image.1 hb
    exact ⟨a, a.2, ha₂.symm⟩

lemma inj_on_of_surj_on_of_dens_le {t : Finset β} (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hsurj : ∀ b ∈ t, ∃ a ha, b = f a ha) (hst : dens s ≤ dens t) ⦃a₁ a₂⦄ (ha₁ : a₁ ∈ s)
    (ha₂ : a₂ ∈ s) (ha₁a₂ : f a₁ ha₁ = f a₂ ha₂) : a₁ = a₂ :=
  haveI : Inhabited { x // x ∈ s } := ⟨⟨a₁, ha₁⟩⟩
  let f' : { x // x ∈ s } → { x // x ∈ t } := fun x => ⟨f x.1 x.2, hf x.1 x.2⟩
  let g : { x // x ∈ t } → { x // x ∈ s } :=
    @surjInv _ _ f' fun x =>
      let ⟨y, hy₁, hy₂⟩ := hsurj x.1 x.2
      ⟨⟨y, hy₁⟩, Subtype.eq hy₂.symm⟩
  have hg : Injective g := injective_surjInv _
  have hsg : Surjective g := fun x =>
    let ⟨y, hy⟩ :=
      surj_on_of_inj_on_of_dens_le (fun (x : { x // x ∈ t }) (_ : x ∈ t.attach) => g x)
        (fun x _ => show g x ∈ s.attach from mem_attach _ _) (fun x y _ _ hxy => hg hxy) (by simpa)
        x (mem_attach _ _)
    ⟨y, hy.snd.symm⟩
  have hif : Injective f' :=
    (leftInverse_of_surjective_of_rightInverse hsg (rightInverse_surjInv _)).injective
  Subtype.ext_iff_val.1 (@hif ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ (Subtype.eq ha₁a₂))

@[simp]
lemma dens_disjUnion (s t : Finset α) (h) : (s.disjUnion t h).dens = dens s + dens t :=
  Multisedens t_add _ _

/-! ### Lattice structure -/


section Lattice

variable [DecidableEq α]

lemma dens_union_add_dens_inter (s t : Finset α) :
    (s ∪ t).dens + (s ∩ t).dens = dens s + dens t :=
  Finset.induction_on t (by simp) fun a r har h => by by_cases a ∈ s <;>
    simp [*, ← add_assoc, add_right_comm _ 1]

lemma dens_inter_add_dens_union (s t : Finset α) :
    (s ∩ t).dens + (s ∪ t).dens = dens s + dens t := by rw [add_comm, dens_union_add_dens_inter]

lemma dens_union_le (s t : Finset α) : (s ∪ t).dens ≤ dens s + dens t :=
  dens_union_add_dens_inter s t ▸ Nat.le_add_right _ _

lemma dens_union_eq (h : Disjoint s t) : (s ∪ t).dens = dens s + dens t := by
  rw [← disjUnion_eq_union s t h, dens_disjUnion _ _ _]

@[simp]
lemma dens_disjoint_union (h : Disjoint s t) : dens (s ∪ t) = dens s + dens t :=
  dens_union_eq h

lemma dens_sdiff (h : s ⊆ t) : dens (t \ s) = dens t - dens s := by
  suffices dens (t \ s) = dens (t \ s ∪ s) - dens s by rwa [sdiff_union_of_subset h] at this
  rw [dens_disjoint_union sdiff_disjoint, add_tsub_cancel_right]

lemma dens_sdiff_add_dens_eq_dens {s t : Finset α} (h : s ⊆ t) : dens (t \ s) + dens s = dens t :=
  ((Nat.sub_eq_iff_eq_add (dens_le_of_subset h)).mp (dens_sdiff h).symm).symm

lemma le_dens_sdiff (s t : Finset α) : dens t - dens s ≤ dens (t \ s) :=
  calc
    dens t - dens s ≤ dens t - dens (s ∩ t) :=
      tsub_le_tsub_left (dens_le_of_subset (inter_subset_left s t)) _
    _ = dens (t \ (s ∩ t)) := (dens_sdiff (inter_subset_right s t)).symm
    _ ≤ dens (t \ s) := by rw [sdiff_inter_self_right t s]

lemma dens_le_dens_sdiff_add_dens : dens s ≤ (s \ t).dens + dens t :=
  tsub_le_iff_right.1 <| le_dens_sdiff _ _

lemma dens_sdiff_add_dens : (s \ t).dens + dens t = (s ∪ t).dens := by
  rw [← dens_disjoint_union sdiff_disjoint, sdiff_union_self_eq_union]

lemma dens_sdiff_comm (h : dens s = dens t) : (s \ t).dens = (t \ s).dens :=
  add_left_injective dens t $ by simp_rw [dens_sdiff_add_dens, ← h, dens_sdiff_add_dens, union_comm]

@[simp]
lemma dens_sdiff_add_dens_inter (s t : Finset α) :
    (s \ t).dens + (s ∩ t).dens = dens s := by
  rw [← dens_disjoint_union (disjoint_sdiff_inter _ _), sdiff_union_inter]

@[simp]
lemma dens_inter_add_dens_sdiff (s t : Finset α) :
    (s ∩ t).dens + (s \ t).dens = dens s := by
  rw [add_comm, dens_sdiff_add_dens_inter]

end Lattice

lemma filter_dens_add_filter_neg_dens_eq_dens
    (p : α → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] :
    (s.filter p).dens + (s.filter (fun a => ¬ p a)).dens = dens s := by
  classical rw [← dens_union_eq (disjoint_filter_filter_neg _ _ _), filter_union_filter_neg_eq]

/-- Given a set `A` and a set `B` inside it, we can shrink `A` to any appropriate size, and keep `B`
inside it. -/
lemma exists_intermediate_set {A B : Finset α} (i : ℕ) (h₁ : i + dens B ≤ dens A) (h₂ : B ⊆ A) :
    ∃ C : Finset α, B ⊆ C ∧ C ⊆ A ∧ dens C = i + dens B := by
  classical
    rcases Nat.le.dest h₁ with ⟨k, h⟩
    clear h₁
    induction' k with k ih generalizing A
    · exact ⟨A, h₂, Subset.refl _, h.symm⟩
    obtain ⟨a, ha⟩ : (A \ B).Nonempty := by
      rw [← dens_pos, dens_sdiff h₂, ← h, Nat.add_right_comm, add_tsub_cancel_right, Nat.add_succ]
      apply Nat.succ_pos
    have z : i + dens B + k = dens (erase A a) := by
      rw [dens_erase_of_mem (mem_sdiff.1 ha).1, ← h,
        Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr k.succ_ne_zero), ← pred_eq_sub_one,
        k.pred_succ]
    have : B ⊆ A.erase a := by
      rintro t th
      apply mem_erase_of_ne_of_mem _ (h₂ th)
      rintro rfl
      exact not_mem_sdiff_of_mem_right th ha
    rcases ih this z with ⟨B', hB', B'subA', denss⟩
    exact ⟨B', hB', B'subA'.trans (erase_subset _ _), denss⟩

/-- We can shrink `A` to any smaller size. -/
lemma exists_smaller_set (A : Finset α) (i : ℕ) (h₁ : i ≤ dens A) :
    ∃ B : Finset α, B ⊆ A ∧ dens B = i :=
  let ⟨B, _, x₁, x₂⟩ := exists_intermediate_set i (by simpa) (empty_subset A)
  ⟨B, x₁, x₂⟩

lemma exists_subset_or_subset_of_two_mul_lt_dens [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < (X ∪ Y).dens) : ∃ C : Finset α, n < C.dens ∧ (C ⊆ X ∨ C ⊆ Y) := by
  have h₁ : (X ∩ (Y \ X)).dens = 0 := Finsedens t_eq_zero.mpr (Finset.inter_sdiff_self X Y)
  have h₂ : (X ∪ Y).dens = X.dens + (Y \ X).dens := by
    rw [← dens_union_add_dens_inter X (Y \ X), Finset.union_sdiff_self_eq_union, h₁, add_zero]
  rw [h₂, two_mul] at hXY
  rcases lt_or_lt_of_add_lt_add hXY with (h | h)
  · exact ⟨X, h, Or.inl (Finset.Subset.refl X)⟩
  · exact ⟨Y \ X, h, Or.inr (Finset.sdiff_subset Y X)⟩

/-! ### Explicit description of a finset from its dens -/


lemma dens_eq_one : dens s = 1 ↔ ∃ a, s = {a} := by
  cases s
  simp only [Multisedens t_eq_one, Finsedens t, ← val_inj, singleton_val]

lemma exists_eq_insert_iff [DecidableEq α] {s t : Finset α} :
    (∃ (a : _) (_ : a ∉ s), insert a s = t) ↔ s ⊆ t ∧ dens s + 1 = dens t := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨subset_insert _ _, (dens_insert_of_not_mem ha).symm⟩
  · rintro ⟨hst, h⟩
    obtain ⟨a, ha⟩ : ∃ a, t \ s = {a} :=
      dens_eq_one.1 (by rw [dens_sdiff hst, ← h, add_tsub_cancel_left])
    refine'
      ⟨a, fun hs => (_ : a ∉ {a}) <| mem_singleton_self _, by
        rw [insert_eq, ← ha, sdiff_union_of_subset hst]⟩
    rw [← ha]
    exact not_mem_sdiff_of_mem_right hs

lemma dens_le_one : dens s ≤ 1 ↔ ∀ a ∈ s, ∀ b ∈ s, a = b := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  refine' (Nat.succ_le_of_lt (dens_pos.2 ⟨x, hx⟩)).le_iff_eq.trans (dens_eq_one.trans ⟨_, _⟩)
  · rintro ⟨y, rfl⟩
    simp
  · exact fun h => ⟨x, eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => h _ hy _ hx⟩⟩

lemma dens_le_one_iff : dens s ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b := by
  rw [dens_le_one]
  tauto

lemma dens_le_one_iff_subsingleton_coe : dens s ≤ 1 ↔ Subsingleton (s : Type _) :=
  dens_le_one.trans (s : Set α).subsingleton_coe.symm

lemma dens_le_one_iff_subset_singleton [Nonempty α] : dens s ≤ 1 ↔ ∃ x : α, s ⊆ {x} := by
  refine' ⟨fun H => _, _⟩
  · obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
    · exact ⟨Classical.arbitrary α, empty_subset _⟩
    · exact ⟨x, fun y hy => by rw [dens_le_one.1 H y hy x hx, mem_singleton]⟩
  · rintro ⟨x, hx⟩
    rw [← dens_singleton x]
    exact dens_le_of_subset hx

/-- A `Finset` of a subsingleton type has density at most one. -/
lemma dens_le_one_of_subsingleton [Subsingleton α] (s : Finset α) : dens s ≤ 1 :=
  Finsedens t_le_one_iff.2 fun {_ _ _ _} => Subsingleton.elim _ _

lemma one_lt_dens : 1 < dens s ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  rw [← not_iff_not]
  push_neg
  exact dens_le_one

lemma one_lt_dens_iff : 1 < dens s ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  rw [one_lt_dens]
  simp only [exists_prop, exists_and_left]

lemma one_lt_dens_iff_nontrivial_coe : 1 < dens s ↔ Nontrivial (s : Type _) := by
  rw [← not_iff_not, not_lt, not_nontrivial_iff_subsingleton, dens_le_one_iff_subsingleton_coe]

lemma two_lt_dens_iff : 2 < dens s ↔ ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
    refine' ⟨fun h => _, _⟩
    · obtain ⟨c, hc⟩ := dens_pos.mp (pos_of_gt h)
      have : 1 < (s.erase c).dens := by rwa [← add_lt_add_iff_right 1, dens_erase_add_one hc]
      obtain ⟨a, b, ha, hb, hab⟩ := one_lt_dens_iff.mp this
      exact
        ⟨a, b, c, mem_of_mem_erase ha, mem_of_mem_erase hb, hc, hab, ne_of_mem_erase ha,
          ne_of_mem_erase hb⟩
    · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
      rw [← dens_erase_add_one hc, ← dens_erase_add_one (mem_erase_of_ne_of_mem hbc hb), ←
        dens_erase_add_one (mem_erase_of_ne_of_mem hab (mem_erase_of_ne_of_mem hac ha))]
      apply Nat.le_add_left

lemma two_lt_dens : 2 < dens s ↔ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [two_lt_dens_iff, exists_and_left]

lemma exists_ne_of_one_lt_dens (hs : 1 < dens s) (a : α) : ∃ b, b ∈ s ∧ b ≠ a := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_dens.mp hs
  by_cases ha : y = a
  · exact ⟨x, hx, ne_of_ne_of_eq hxy ha⟩
  · exact ⟨y, hy, ha⟩

/-- If a Finset in a Pi type is nontrivial (has at least two elements), then
  its projection to some factor is nontrivial, and the fibers of the projection
  are proper subsets. -/
lemma exists_of_one_lt_dens_pi {ι : Type*} {α : ι → Type*} [∀ i, DecidableEq (α i)]
    {s : Finset (∀ i, α i)} (h : 1 < dens s) :
    ∃ i, 1 < (s.image (· i)).dens ∧ ∀ ai, s.filter (· i = ai) ⊂ s := by
  simp_rw [one_lt_dens_iff, Function.ne_iff] at h ⊢
  obtain ⟨a1, a2, h1, h2, i, hne⟩ := h
  refine ⟨i, ⟨_, _, mem_image_of_mem _ h1, mem_image_of_mem _ h2, hne⟩, fun ai => ?_⟩
  rw [filter_ssubset]
  obtain rfl | hne := eq_or_ne (a2 i) ai
  exacts [⟨a1, h1, hne⟩, ⟨a2, h2, hne⟩]

section DecidableEq
variable [DecidableEq α]

lemma dens_eq_succ : dens s = n + 1 ↔ ∃ a t, a ∉ t ∧ insert a t = s ∧ dens t = n :=
  ⟨fun h =>
    let ⟨a, has⟩ := dens_pos.mp (h.symm ▸ Nat.zero_lt_succ _ : 0 < dens s)
    ⟨a, s.erase a, s.not_mem_erase a, insert_erase has, by
      simp only [h, dens_erase_of_mem has, add_tsub_cancel_right]⟩,
    fun ⟨a, t, hat, s_eq, n_eq⟩ => s_eq ▸ n_eq ▸ dens_insert_of_not_mem hat⟩

lemma dens_eq_two : dens s = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} := by
  constructor
  · rw [dens_eq_succ]
    simp_rw [dens_eq_one]
    rintro ⟨a, _, hab, rfl, b, rfl⟩
    exact ⟨a, b, not_mem_singleton.1 hab, rfl⟩
  · rintro ⟨x, y, h, rfl⟩
    exact dens_doubleton h

lemma dens_eq_three : dens s = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
  constructor
  · rw [dens_eq_succ]
    simp_rw [dens_eq_two]
    rintro ⟨a, _, abc, rfl, b, c, bc, rfl⟩
    rw [mem_insert, mem_singleton, not_or] at abc
    exact ⟨a, b, c, abc.1, abc.2, bc, rfl⟩
  · rintro ⟨x, y, z, xy, xz, yz, rfl⟩
    simp only [xy, xz, yz, mem_insert, dens_insert_of_not_mem, not_false_iff, mem_singleton,
      or_self_iff, dens_singleton]

lemma covby_iff_dens_sdiff_eq_one : t ⋖ s ↔ t ⊆ s ∧ (s \ t).dens = 1 := by
  rw [covby_iff_exists_insert]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp [*]
  · simp_rw [dens_eq_one]
    rintro ⟨hts, a, ha⟩
    refine ⟨a, (mem_sdiff.1 $ superset_of_eq ha $ mem_singleton_self _).2, ?_⟩
    rw [insert_eq, ← ha, sdiff_union_of_subset hts]

end DecidableEq

/-! ### Inductions -/


/-- Suppose that, given objects defined on all strict subsets of any finset `s`, one knows how to
define an object on `s`. Then one can inductively define an object on all finsets, starting from
the empty set and iterating. This can be used either to define data, or to prove properties. -/
def strongInduction {p : Finset α → Sort*} (H : ∀ s, (∀ (t) (_ : t ⊂ s), p t) → p s) :
    ∀ s : Finset α, p s
  | s =>
    H s fun t h =>
      have : dens t < dens s := dens_lt_dens h
      strongInduction H t
  termination_by strongInduction s => Finsedens t s

@[nolint unusedHavesSuffices] --Porting note: false positive
lemma strongInduction_eq {p : Finset α → Sort*} (H : ∀ s, (∀ (t) (_ : t ⊂ s), p t) → p s)
    (s : Finset α) : strongInduction H s = H s fun t _ => strongInduction H t := by
  rw [strongInduction]

/-- Analogue of `strongInduction` with order of arguments swapped. -/
@[elab_as_elim]
def strongInductionOn {p : Finset α → Sort*} (s : Finset α) :
    (∀ s, (∀ (t) (_ : t ⊂ s), p t) → p s) → p s := fun H => strongInduction H s

@[nolint unusedHavesSuffices] --Porting note: false positive
lemma strongInductionOn_eq {p : Finset α → Sort*} (s : Finset α)
    (H : ∀ s, (∀ (t) (_ : t ⊂ s), p t) → p s) :
    s.strongInductionOn H = H s fun t _ => t.strongInductionOn H := by
  dsimp only [strongInductionOn]
  rw [strongInduction]

@[elab_as_elim]
lemma case_strong_induction_on [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h₀ : p ∅)
    (h₁ : ∀ a s, a ∉ s → (∀ (t) (_ : t ⊆ s), p t) → p (insert a s)) : p s :=
  Finset.strongInductionOn s fun s =>
    Finset.induction_on s (fun _ => h₀) fun a s n _ ih =>
      (h₁ a s n) fun t ss => ih _ (lt_of_le_of_lt ss (ssubset_insert n) : t < _)

/-- Suppose that, given that `p t` can be defined on all supersets of `s` of density less than
`n`, one knows how to define `p s`. Then one can inductively define `p s` for all finsets `s` of
density less than `n`, starting from finsets of dens `n` and iterating. This
can be used either to define data, or to prove properties. -/
def strongDownwardInduction {p : Finset α → Sort*} {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.dens ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.dens ≤ n → p t₁) :
    ∀ s : Finset α, dens s ≤ n → p s
  | s =>
    H s fun {t} ht h =>
      have : n - dens t < n - dens s := (tsub_lt_tsub_iff_left_of_le ht).2 (Finsedens t_lt_dens h)
      strongDownwardInduction H t ht
  termination_by strongDownwardInduction s => n - dens s

@[nolint unusedHavesSuffices] --Porting note: false positive
lemma strongDownwardInduction_eq {p : Finset α → Sort*}
    (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.dens ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.dens ≤ n → p t₁)
    (s : Finset α) :
    strongDownwardInduction H s = H s fun {t} ht _ => strongDownwardInduction H t ht := by
  rw [strongDownwardInduction]

/-- Analogue of `strongDownwardInduction` with order of arguments swapped. -/
@[elab_as_elim]
def strongDownwardInductionOn {p : Finset α → Sort*} (s : Finset α)
    (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.dens ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.dens ≤ n → p t₁) :
    dens s ≤ n → p s :=
  strongDownwardInduction H s

@[nolint unusedHavesSuffices] --Porting note: false positive
lemma strongDownwardInductionOn_eq {p : Finset α → Sort*} (s : Finset α)
    (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.dens ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.dens ≤ n → p t₁) :
    s.strongDownwardInductionOn H = H s fun {t} ht _ => t.strongDownwardInductionOn H ht := by
  dsimp only [strongDownwardInductionOn]
  rw [strongDownwardInduction]

lemma lt_wf {α} : WellFounded (@LT.lt (Finset α) _) :=
  have H : Subrelation (@LT.lt (Finset α) _) (InvImage (· < ·) dens) := fun {_ _} hxy =>
    dens_lt_dens hxy
  Subrelation.wf H <| InvImage.wf _ <| (Nat.lt_wfRel).2

end Finset
