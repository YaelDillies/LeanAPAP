import algebra.big_operators.ring
import data.fintype.card
import data.fintype.big_operators

open_locale big_operators

namespace finset
variables {α β : Type*}

-- TODO: This is a copy of `finset.prod_univ_sum` with patched universe variables
/-- The product over `univ` of a sum can be written as a sum over the product of sets,
`fintype.pi_finset`. `finset.prod_sum` is an alternative statement when the product is not
over `univ` -/
lemma prod_univ_sum' [decidable_eq α] [fintype α] [comm_semiring β] {δ : α → Type*}
  [Π a, decidable_eq (δ a)] {t : Π a, finset (δ a)} {f : Π a, δ a → β} :
  ∏ a, ∑ b in t a, f a b = ∑ p in fintype.pi_finset t, ∏ x, f x (p x) :=
by simp only [finset.prod_attach_univ, prod_sum, finset.sum_univ_pi]

end finset

namespace finset
variables {α β : Type*} [comm_semiring β] [decidable_eq α]

lemma pow_sum (s : finset α) (f : α → β) (n : ℕ) :
  (∑ a in s, f a) ^ n = ∑ p in fintype.pi_finset (λ i : fin n, s), ∏ i, f (p i) :=
by convert @prod_univ_sum' (fin n) _ _ _ _ _ _ (λ i, s) (λ i d, f d); simp

end finset
