import Mathlib.Data.Finset.Pointwise
import LeanAPAP.Mathlib.Algebra.BigOperators.Basic

/-!
# Wide diagonal
-/

open scoped BigOperators Pointwise

namespace Finset
variable {α : Type*} [DecidableEq α] {s : Finset α} {k : ℕ}

def wideDiag (k : ℕ) (s : Finset α) : Finset (Fin k → α) := s.image fun i _ ↦ i

lemma mem_wideDiag {k : ℕ} {x : Fin k → α} :
    x ∈ s.wideDiag k ↔ ∃ i ∈ s, (fun _ ↦ i) = x := mem_image

def fintypeWideDiag (α : Type*) [DecidableEq α] [Fintype α] (k : ℕ) : Finset (Fin k → α) :=
  univ.wideDiag k

lemma mem_fintypeWideDiag [Fintype α] {k : ℕ} {x : Fin k → α} :
    x ∈ fintypeWideDiag α k ↔ ∃ i, (fun _ ↦ i) = x :=
  mem_wideDiag.trans (by simp)

@[simp] lemma card_wideDiag (hk : k ≠ 0) (s : Finset α) : (s.wideDiag k).card = s.card := by
  cases k
  · cases hk rfl
  rw [Finset.wideDiag, card_image_of_injective]
  exact fun i j h ↦ congr_fun h 0

section Add
variable [Add α]

lemma big_shifts_step1 (L : Finset (Fin k → α)) (hk : k ≠ 0) :
    ∑ x in L + s.wideDiag k, ∑ l in L, ∑ s in s.wideDiag k, (if l + s = x then 1 else 0)
      = L.card * s.card := by
  simp only [@sum_comm _ _ _ _ (L + _), sum_ite_eq]
  rw [sum_const_nat]
  intro l hl
  rw [sum_const_nat, mul_one, Finset.card_wideDiag hk]
  exact fun s hs ↦ if_pos (Finset.add_mem_add hl hs)

end Add

variable [AddCommGroup α] [Fintype α]

lemma reindex_count (L : Finset (Fin k → α)) (hk : k ≠ 0) (hL' : L.Nonempty) (l₁ : Fin k → α) :
    ∑ l₂ in L, ite (l₁ - l₂ ∈ fintypeWideDiag α k) 1 0 =
      (univ.filter fun t ↦ (l₁ - fun _ ↦ t) ∈ L).card :=
  calc
    ∑ l₂ : Fin k → α in L, ite (l₁ - l₂ ∈ fintypeWideDiag α k) 1 0 =
        ∑ l₂ in L, ∑ t : α, ite ((l₁ - fun _ ↦ t) = l₂) 1 0 := by
      refine' sum_congr rfl fun l₂ hl₂ ↦ _
      rw [Fintype.sum_ite_exists]
      simp only [mem_fintypeWideDiag, @eq_comm _ l₁, eq_sub_iff_add_eq, sub_eq_iff_eq_add']
      rintro i j h rfl
      cases k
      · simp at hk
      · simpa using congr_fun h 0
    _ = (univ.filter fun t ↦ (l₁ - fun _ ↦ t) ∈ L).card := by
      simp only [sum_comm, sum_ite_eq, card_eq_sum_ones, sum_filter]

end Finset
