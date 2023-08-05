import algebra.big_operators.basic

/-!
## TODO

* More explicit arguments to `finset.sum_attach`
-/

localized "notation `∑` binders ` in ` s ` with ` p:(scoped:30 p, p) `, ` r:(scoped:67 f, finset.sum (s.filter p) f) := r" in big_operators
localized "notation `∑` binders ` with ` p:(scoped:30 p, p) `, ` r:(scoped:67 f, finset.sum (finset.univ.filter p) f) := r" in big_operators

open_locale big_operators

namespace finset
variables {α β γ : Type*} [comm_monoid β] {s s₁ s₂ : finset α} {t : finset γ} {f : α → β}
  {g : γ → β}

@[to_additive]
lemma prod_mul_prod_comm (f g h i : α → β) :
  (∏ a in s, f a * g a) * (∏ a in s, h a * i a) = (∏ a in s, f a * h a) * (∏ a in s, g a * i a) :=
by simp_rw [prod_mul_distrib, mul_mul_mul_comm]

@[to_additive]
lemma prod_nbij (i : α → γ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
  (i_inj : ∀ a₁ a₂, a₁ ∈ s → a₂ ∈ s → i a₁ = i a₂ → a₁ = a₂) (i_surj : ∀ b ∈ t, ∃ a ∈ s, b = i a) :
  ∏ x in s, f x = ∏ x in t, g x :=
prod_bij (λ a _, i a) hi h i_inj i_surj

@[to_additive]
lemma prod_nbij' (i : α → γ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
  (j : γ → α) (hj : ∀ a ∈ t, j a ∈ s)
  (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a) :
  ∏ x in s, f x = ∏ x in t, g x :=
prod_bij' (λ a _, i a) hi h (λ b _, j b) hj left_inv right_inv

@[to_additive]
lemma prod_ite_one' (s : finset α) (p : α → Prop) [decidable_pred p]
  (h : ∀ i j ∈ s, p i → p j → i = j) (a : β) : ∏ i in s, ite (p i) a 1 = ite (∃ i ∈ s, p i) a 1 :=
prod_ite_one (λ i hi j hj, by simpa only [function.on_fun_apply, Prop.disjoint_iff, not_imp_not,
  and_imp] using h i hi j hj) _

variables [decidable_eq α]

@[to_additive] lemma prod_union_eq_left (hs : ∀ a ∈ s₂, a ∉ s₁ → f a = 1) :
  ∏ a in s₁ ∪ s₂, f a = ∏ a in s₁, f a :=
eq.symm $ prod_subset (subset_union_left _ _) $ λ a ha ha',
  hs _ ((mem_union.1 ha).resolve_left ha') ha'

@[to_additive] lemma prod_union_eq_right (hs : ∀ a ∈ s₁, a ∉ s₂ → f a = 1) :
  ∏ a in s₁ ∪ s₂, f a = ∏ a in s₂, f a :=
by rw [union_comm, prod_union_eq_left hs]

end finset

open finset

namespace fintype
variables {α β : Type*} [fintype α]

section comm_monoid
variables [comm_monoid β] (a : β)

@[to_additive]
lemma prod_ite_exists (p : α → Prop) [decidable_pred p] (h : ∀ i j, p i → p j → i = j) (a : β) :
  ∏ i, ite (p i) a 1 = ite (∃ i, p i) a 1 :=
by simp [prod_ite_one' univ p (by simpa using h)]

variables [decidable_eq α]

@[simp, to_additive] lemma prod_dite_eq (a : α) (b : Π x, a = x → β) :
  ∏ x, (if h : a = x then b x h else 1) = b a rfl :=
by simp

@[simp, to_additive] lemma prod_dite_eq' (a : α) (b : Π x, x = a → β) :
  ∏ x, (if h : x = a then b x h else 1) = b a rfl :=
by simp

@[simp, to_additive] lemma prod_ite_eq (a : α) (b : α → β) :
  ∏ x, (if a = x then b x else 1) = b a :=
by simp

@[simp, to_additive] lemma prod_ite_eq' [decidable_eq α] (a : α) (b : α → β) :
  ∏ x, (if x = a then b x else 1) = b a :=
by simp

end comm_monoid

variables [comm_monoid_with_zero β] {p : α → Prop} [decidable_pred p]

lemma prod_boole : ∏ i, ite (p i) (1 : β) 0 = ite (∀ i, p i) 1 0 := by simp [finset.prod_boole]

end fintype
