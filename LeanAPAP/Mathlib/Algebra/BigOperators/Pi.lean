import Mathlib.Algebra.BigOperators.Pi
import LeanAPAP.Mathlib.Algebra.BigOperators.Ring
import LeanAPAP.Mathlib.Data.Fintype.Pi

#align_import mathlib.algebra.big_operators.pi

open Finset

open scoped BigOperators

namespace Fintype
variable {α β : Type*} {δ : α → Type*} [DecidableEq α] [Fintype α] [DecidableEq β]
  [∀ a, DecidableEq (δ a)]

lemma filter_piFinset_card_of_mem [∀ a, DecidableEq (δ a)] (t : ∀ a, Finset (δ a)) (a : α)
    (x : δ a) (hx : x ∈ t a) :
    ((piFinset t).filterₓ λ f : ∀ a, δ a => f a = x).card = ∏ b in univ.eraseₓ a, (t b).card := by
  let t' : ∀ a, Finset (δ a) := λ a' =>
    if h : a = a' then {(@Eq.ndrec _ _ δ x _ h : δ a')} else t a'
  have : (t' a).card = 1 := by simp [t']
  have h₁ : ∏ b in univ.erase a, (t b).card = ∏ b, (t' b).card := by
    rw [← @prod_erase ℕ α _ _ univ (λ b => (t' b).card) a this]
    refine' Finset.prod_congr rfl _
    intro b hb
    simp only [mem_erase, Ne.def, mem_univ, and_true_iff] at hb
    simp only [t', dif_neg (Ne.symm hb)]
  have h₂ : ∏ b, (t' b).card = ∏ b, ∑ i in t' b, 1 := by simp
  rw [h₁, h₂, prod_univ_sum']
  simp only [prod_const_one, ← Finset.card_eq_sum_ones]
  congr 1
  ext f
  simp only [mem_filter, mem_pi_finset, t']
  refine' ⟨_, λ h => _⟩
  · rintro ⟨hf, rfl⟩ b
    split_ifs with h₁ h₁
    · cases h₁
      simp
    · exact hf _
  have : f a = x := by simpa using h a
  refine' ⟨λ b => _, this⟩
  obtain rfl | hab := eq_or_ne a b
  · rwa [this]
  · simpa [dif_neg hab] using h b

lemma filter_piFinset_const_card_of_mem (t : Finset β) (a : α) (x : β) (hx : x ∈ t) :
    ((piFinset λ _ => t).filterₓ λ f : α → β => f a = x).card = t.card ^ (card α - 1) := by
  rw [filter_pi_finset_card_of_mem, prod_const t.card, card_erase_of_mem, card_univ]
  · simp
  · exact hx

lemma filter_piFinset_card (t : ∀ a, Finset (δ a)) (a : α) (x : δ a) :
    ((piFinset t).filterₓ λ f : ∀ a, δ a => f a = x).card =
      if x ∈ t a then ∏ b in univ.eraseₓ a, (t b).card else 0 := by
  split_ifs
  · rw [filter_pi_finset_card_of_mem _ _ _ h]
  · rw [filter_pi_finset_of_not_mem _ _ _ h, Finset.card_empty]

lemma filter_piFinset_const_card (t : Finset β) (a : α) (x : β) :
    ((piFinset λ _ => t).filterₓ λ f : α → β => f a = x).card =
      if x ∈ t then t.card ^ (card α - 1) else 0 := by rw [filter_pi_finset_card, prod_const t.card, card_erase_of_mem, card_univ]; simp

end Fintype
