import algebra.big_operators.ring
import data.fintype.big_operators
import data.fintype.prod

/-!
## TODO

More explicit arguments to `finset.mul_sum`/`finset.sum_mul`
-/

open_locale big_operators

namespace finset
variables {ι α β : Type*}

-- TODO: This is a copy of `finset.prod_univ_sum` with patched universe variables
/-- The product over `univ` of a sum can be written as a sum over the product of sets,
`fintype.pi_finset`. `finset.prod_sum` is an alternative statement when the product is not
over `univ` -/
lemma prod_univ_sum' [decidable_eq α] [fintype α] [comm_semiring β] {δ : α → Type*}
  [Π a, decidable_eq (δ a)] {t : Π a, finset (δ a)} {f : Π a, δ a → β} :
  ∏ a, ∑ b in t a, f a b = ∑ p in fintype.pi_finset t, ∏ x, f x (p x) :=
by simp only [finset.prod_attach_univ, prod_sum, finset.sum_univ_pi]

lemma sum_prod_pi_finset [decidable_eq ι] [fintype ι] [comm_semiring β] (s : finset α)
  (g : ι → α → β) :
  ∑ f in fintype.pi_finset (λ _ : ι, s), ∏ i, g i (f i) = ∏ i, ∑ x in s, g i x :=
by { classical, rw ←@finset.prod_univ_sum' ι }

section comm_monoid
variables [comm_monoid β]

lemma pow_sum (s : finset α) (f : α → ℕ) (m : β) : ∏ i in s, m ^ f i = m ^ ∑ i in s, f i :=
by induction s using finset.cons_induction_on with a s has ih; simp [*, pow_add]

end comm_monoid

section comm_semiring
variables [comm_semiring β]

lemma sum_pow' (s : finset α) (f : α → β) (n : ℕ) :
  (∑ a in s, f a) ^ n = ∑ p in fintype.pi_finset (λ i : fin n, s), ∏ i, f (p i) :=
by classical; convert @prod_univ_sum' (fin n) _ _ _ _ _ _ (λ i, s) (λ i d, f d); simp

end comm_semiring
end finset

namespace fintype
variables {α β : Type*} [fintype α] [comm_semiring β]

lemma sum_pow (f : α → β) (n : ℕ) : (∑ a, f a) ^ n = ∑ p : fin n → α, ∏ i, f (p i) :=
by simp [finset.sum_pow']

lemma sum_mul_sum {ι₁ : Type*} {ι₂ : Type*} [fintype ι₁] [fintype ι₂] (f₁ : ι₁ → β) (f₂ : ι₂ → β) :
  (∑ x₁, f₁ x₁) * (∑ x₂, f₂ x₂) = ∑ p : ι₁ × ι₂, f₁ p.1 * f₂ p.2 :=
finset.sum_mul_sum _ _ _ _

end fintype

open finset

namespace nat
variables {α : Type*} {s : finset α} {f : α → ℕ} {n : ℕ}

protected lemma sum_div (hf : ∀ i ∈ s, n ∣ f i) : (∑ i in s, f i) / n = ∑ i in s, f i / n :=
begin
  obtain rfl | hn := n.eq_zero_or_pos,
  { simp },
  rw [nat.div_eq_iff_eq_mul_left hn (dvd_sum hf), sum_mul],
  refine sum_congr rfl (λ s hs, _),
  rw nat.div_mul_cancel (hf _ hs),
end

end nat
