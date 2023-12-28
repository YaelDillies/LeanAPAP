import Mathlib.Data.Fintype.BigOperators

open Finset

namespace Fintype
variable {α β : Type*} {δ : α → Type*} {s : Finset α} {n : ℕ}

@[reducible]
def piFinsetConst (s : Finset α) (n : ℕ) := piFinset fun _ : Fin n ↦ s

infixl:70 "^^" => piFinsetConst

protected lemma _root_.Finset.Nonempty.piFinsetConst (hs : s.Nonempty) : (s ^^ n).Nonempty :=
  piFinset_nonempty.2 fun _ ↦ hs

@[simp] lemma card_piFinsetConst (s : Finset α) (n : ℕ) : (s ^^ n).card = s.card ^ n := by
  simp [piFinsetConst, card_piFinset]

variable [DecidableEq α] [Fintype α]

lemma image_piFinset (t : ∀ a, Finset (δ a)) (a : α) [DecidableEq (δ a)]
    (ht : ∀ b, a ≠ b → (t b).Nonempty) : ((piFinset t).image fun f ↦ f a) = t a := by
  ext x
  simp only [mem_image, mem_piFinset, exists_prop]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf _
  intro h
  choose f hf using ht
  refine' ⟨fun b ↦ if h : a = b then (@Eq.ndrec α a δ x _ h : δ b) else f _ h, fun b ↦ _, by simp⟩
  dsimp
  split
  · cases ‹_›
    exact h
  · exact hf _ _

lemma image_piFinset_const [DecidableEq β] (t : Finset β) (a : α) :
    ((piFinset fun _i : α ↦ t).image fun f ↦ f a) = t := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · haveI : Nonempty α := ⟨a⟩
    simp
  · exact image_piFinset (fun _ ↦ t) a fun _ _ ↦ ht

-- works better for rewrites
lemma filter_piFinset_const_of_not_mem [DecidableEq β] (t : Finset β) (a : α) (x : β)
    (hx : x ∉ t) : ((piFinset fun _ ↦ t).filter fun f : α → β ↦ f a = x) = ∅ :=
  filter_piFinset_of_not_mem _ _ _ hx

end Fintype
