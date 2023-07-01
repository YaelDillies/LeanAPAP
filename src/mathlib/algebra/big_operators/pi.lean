import algebra.big_operators.pi
import mathlib.algebra.big_operators.ring
import mathlib.data.fintype.pi

open finset
open_locale big_operators

namespace fintype
variables {α β : Type*} {δ : α → Type*} [decidable_eq α] [fintype α] [decidable_eq β]
  [Π a, decidable_eq (δ a)]

lemma filter_pi_finset_card_of_mem [Π a, decidable_eq (δ a)] (t : Π a, finset (δ a)) (a : α)
  (x : δ a) (hx : x ∈ t a) :
  ((pi_finset t).filter (λ f : Π a, δ a, f a = x)).card =
    ∏ b in univ.erase a, (t b).card :=
begin
  let t' : Π a, finset (δ a) :=
    λ a', if h : a = a' then {(@eq.rec _ _ δ x _ h : δ a')} else t a',
  have : (t' a).card = 1,
  { simp [t'] },
  have h₁ : ∏ b in univ.erase a, (t b).card = ∏ b, (t' b).card,
  { rw ←@prod_erase ℕ α _ _ univ (λ b, (t' b).card) a this,
    refine finset.prod_congr rfl _,
    intros b hb,
    simp only [mem_erase, ne.def, mem_univ, and_true] at hb,
    simp only [t', dif_neg (ne.symm hb)] },
  have h₂ : ∏ b, (t' b).card = ∏ b, ∑ i in t' b, 1,
  { simp },
  rw [h₁, h₂, prod_univ_sum'],
  simp only [prod_const_one, ←finset.card_eq_sum_ones],
  congr' 1,
  ext f,
  simp only [mem_filter, mem_pi_finset, t'],
  refine ⟨_, λ h, _⟩,
  { rintro ⟨hf, rfl⟩ b,
    split_ifs with h₁ h₁,
    { cases h₁,
      simp },
    { exact hf _ } },
  have : f a = x, { simpa using h a },
  refine ⟨λ b, _, this⟩,
  obtain rfl | hab := eq_or_ne a b,
  { rwa this },
  { simpa [dif_neg hab] using h b }
end

lemma filter_pi_finset_const_card_of_mem (t : finset β) (a : α) (x : β)
  (hx : x ∈ t) :
  ((pi_finset (λ _, t)).filter (λ f : α → β, f a = x)).card = t.card ^ (card α - 1) :=
begin
  rw [filter_pi_finset_card_of_mem, prod_const t.card, card_erase_of_mem, card_univ],
  { simp },
  { exact hx }
end

lemma filter_pi_finset_card (t : Π a, finset (δ a)) (a : α) (x : δ a) :
  ((pi_finset t).filter (λ f : Π a, δ a, f a = x)).card =
    if x ∈ t a then ∏ b in univ.erase a, (t b).card else 0 :=
begin
  split_ifs,
  { rw filter_pi_finset_card_of_mem _ _ _ h },
  { rw [filter_pi_finset_of_not_mem _ _ _ h, finset.card_empty] }
end

lemma filter_pi_finset_const_card (t : finset β) (a : α) (x : β) :
  ((pi_finset (λ _, t)).filter (λ f : α → β, f a = x)).card =
  if x ∈ t then t.card ^ (card α - 1) else 0 :=
by { rw [filter_pi_finset_card, prod_const t.card, card_erase_of_mem, card_univ], simp }

end fintype
