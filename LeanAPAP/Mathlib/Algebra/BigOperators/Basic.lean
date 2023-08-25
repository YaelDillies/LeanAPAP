import Mathlib.Algebra.BigOperators.Basic

#align_import mathlib.algebra.big_operators.basic

/-!
## TODO

* More explicit arguments to `finset.sum_attach`
-/

scoped[BigOperators]
  notation3"∑ "(...)" in "s" with "p:30:(scoped p => p)", "r:67:(scoped f =>
    Finset.sum s.filterₓ p f) => r

scoped[BigOperators]
  notation3"∑ "(...)" with "p:30:(scoped p => p)", "r:67:(scoped f =>
    Finset.sum Finset.univ.filterₓ p f) => r

open scoped BigOperators

namespace Finset
variable {α β γ : Type*} [CommMonoid β] {s s₁ s₂ : Finset α} {t : Finset γ} {f : α → β} {g : γ → β}

@[to_additive]
lemma prod_mul_prod_comm (f g h i : α → β) :
    (∏ a in s, f a * g a) * ∏ a in s, h a * i a = (∏ a in s, f a * h a) * ∏ a in s, g a * i a := by
  simp_rw [prod_mul_distrib, mul_mul_mul_comm]

@[to_additive]
lemma prod_nbij (i : α → γ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
    (i_inj : ∀ a₁ a₂, a₁ ∈ s → a₂ ∈ s → i a₁ = i a₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ∈ s, b = i a) : ∏ x in s, f x = ∏ x in t, g x :=
  prod_bij (λ a _ => i a) hi h i_inj i_surj

@[to_additive]
lemma prod_nbij' (i : α → γ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a)) (j : γ → α)
    (hj : ∀ a ∈ t, j a ∈ s) (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a) :
    ∏ x in s, f x = ∏ x in t, g x :=
  prod_bij' (λ a _ => i a) hi h (λ b _ => j b) hj left_inv right_inv

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (i j «expr ∈ » s) -/
@[to_additive]
lemma prod_ite_one' (s : Finset α) (p : α → Prop) [DecidablePred p]
    (h : ∀ (i) (_ : i ∈ s) (j) (_ : j ∈ s), p i → p j → i = j) (a : β) :
    ∏ i in s, ite (p i) a 1 = ite (∃ i ∈ s, p i) a 1 :=
  prod_ite_one
    (λ i hi j hj => by
      simpa only [Function.onFun_apply, Prop.disjoint_iff, not_imp_not, and_imp] using h i hi j hj)
    _

variable [DecidableEq α]

@[to_additive]
lemma prod_union_eq_left (hs : ∀ a ∈ s₂, a ∉ s₁ → f a = 1) :
    ∏ a in s₁ ∪ s₂, f a = ∏ a in s₁, f a :=
  Eq.symm <|
    prod_subset (subset_union_left _ _) λ a ha ha' => hs _ ((mem_union.1 ha).resolve_left ha') ha'

@[to_additive]
lemma prod_union_eq_right (hs : ∀ a ∈ s₁, a ∉ s₂ → f a = 1) :
    ∏ a in s₁ ∪ s₂, f a = ∏ a in s₂, f a := by rw [union_comm, prod_union_eq_left hs]

@[to_additive (attr := simp)]
lemma prod_diag (s : Finset α) (f : α × α → β) : ∏ i in s.diag, f i = ∏ i in s, f (i, i) :=
  Eq.symm <|
    prod_nbij (λ i => (i, i)) (λ i hi => mem_diag.2 ⟨hi, rfl⟩) (λ i _ => rfl)
      (λ i j _ _ h => (Prod.ext_iff.1 h).1) λ i hi =>
      ⟨i.1, (mem_diag.1 hi).1, Prod.ext rfl (mem_diag.1 hi).2.symm⟩

end Finset

open Finset

namespace Fintype
variable {α β : Type*} [Fintype α]

section CommMonoid
variable [CommMonoid β] (a : β)

@[to_additive]
lemma prod_ite_exists (p : α → Prop) [DecidablePred p] (h : ∀ i j, p i → p j → i = j) (a : β) :
    ∏ i, ite (p i) a 1 = ite (∃ i, p i) a 1 := by simp [prod_ite_one' univ p (by simpa using h)]

variable [DecidableEq α]

@[to_additive (attr := simp)]
lemma prod_dite_eq (a : α) (b : ∀ x, a = x → β) :
    (∏ x, if h : a = x then b x h else 1) = b a rfl := by simp

@[to_additive (attr := simp)]
lemma prod_dite_eq' (a : α) (b : ∀ x, x = a → β) :
    (∏ x, if h : x = a then b x h else 1) = b a rfl := by simp

@[to_additive (attr := simp)]
lemma prod_ite_eq (a : α) (b : α → β) : (∏ x, if a = x then b x else 1) = b a := by simp

@[to_additive (attr := simp)]
lemma prod_ite_eq' [DecidableEq α] (a : α) (b : α → β) : (∏ x, if x = a then b x else 1) = b a := by simp

end CommMonoid

variable [CommMonoidWithZero β] {p : α → Prop} [DecidablePred p]

lemma prod_boole : ∏ i, ite (p i) (1 : β) 0 = ite (∀ i, p i) 1 0 := by simp [Finset.prod_boole]

end Fintype
