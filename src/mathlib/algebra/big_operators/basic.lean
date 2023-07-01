import algebra.big_operators.basic

open_locale big_operators

namespace finset
variables {α β γ : Type*} [add_comm_monoid β] {s : finset α} {t : finset γ} {f : α → β} {g : γ → β}

lemma sum_nbij (i : α → γ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
  (i_inj : ∀ a₁ a₂, a₁ ∈ s → a₂ ∈ s → i a₁ = i a₂ → a₁ = a₂) (i_surj : ∀ b ∈ t, ∃ a ∈ s, b = i a) :
  (∑ x in s, f x) = (∑ x in t, g x) :=
sum_bij (λ a _, i a) hi h i_inj i_surj

lemma sum_nbij' (i : α → γ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
  (j : γ → α) (hj : ∀ a ∈ t, j a ∈ s)
  (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a) :
  (∑ x in s, f x) = (∑ x in t, g x) :=
sum_bij' (λ a _, i a) hi h (λ b _, j b) hj left_inv right_inv

lemma sum_ite_zero' (s : finset α) (p : α → Prop) [decidable_pred p]
  (h : ∀ i j ∈ s, p i → p j → i = j) : ∑ i in s, ite (p i) 1 0 = ite (∃ i ∈ s, p i) 1 0 :=
sum_ite_zero (λ i hi j hj, by simpa only [function.on_fun_apply, Prop.disjoint_iff, not_imp_not,
  and_imp] using h i hi j hj) _

end finset

open finset

namespace fintype
variables {α β : Type*} [fintype α] [comm_monoid_with_zero β] {p : α → Prop} [decidable_pred p]

lemma prod_boole : ∏ i, ite (p i) (1 : β) 0 = ite (∀ i, p i) 1 0 := by simp [finset.prod_boole]

lemma sum_ite_exists (p : α → Prop) [decidable_pred p] (h : ∀ i j, p i → p j → i = j) :
  ∑ i, ite (p i) 1 0 = ite (∃ i, p i) 1 0 :=
by simp [sum_ite_zero' univ p (by simpa using h)]

end fintype
