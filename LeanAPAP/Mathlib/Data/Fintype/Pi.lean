import Mathlib.Data.Finset.NAry
import Mathlib.Data.Fintype.Pi

#align_import mathlib.data.fintype.pi

open Finset

namespace Fintype
variable {α : Type*} {β γ : α → Type*} [Fintype α] [DecidableEq α] [∀ a, DecidableEq (γ a)]

@[simp]
lemma piFinset_of_isEmpty [IsEmpty α] (s : ∀ a, Finset (β a)) : piFinset s = univ :=
  eq_univ_of_forall λ _ => by simp

lemma piFinset_image (f : ∀ a, β a → γ a) (s : ∀ a, Finset (β a)) :
    (piFinset λ a => image (f a) (s a)) =
      image (λ (b : ∀ a, β a) a => f _ (b a)) (piFinset s) := by ext <;> simp only [mem_pi_finset, mem_image, Classical.skolem, forall_and, Function.funext_iff]

end Fintype

namespace Fintype
variable {α : Type*} {β γ δ : α → Type*} [Fintype α] [DecidableEq α] [∀ a, DecidableEq (δ a)]

lemma piFinset_image₂ (f : ∀ a, β a → γ a → δ a) (s : ∀ a, Finset (β a)) (t : ∀ a, Finset (γ a)) :
    (piFinset λ a => image₂ (f a) (s a) (t a)) =
      image₂ (λ (b : ∀ a, β a) (c : ∀ a, γ a) a => f _ (b a) (c a)) (piFinset s) (piFinset t) := by
  ext <;> simp only [mem_pi_finset, mem_image₂, Classical.skolem, forall_and, Function.funext_iff]

end Fintype

namespace Fintype
variable {α β : Type*} {δ : α → Type*}

@[reducible]
def piFinsetConst (s : Finset α) (n : ℕ) :=
  piFinset λ _ : Fin n => s

infixl:70 "^^" => piFinsetConst

variable [DecidableEq α] [Fintype α]

lemma image_piFinset (t : ∀ a, Finset (δ a)) (a : α) [DecidableEq (δ a)]
    (ht : ∀ b, a ≠ b → (t b).Nonempty) : ((piFinset t).image λ f => f a) = t a := by
  ext x
  simp only [mem_image, mem_pi_finset, exists_prop]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf _
  intro h
  choose f hf using ht
  refine' ⟨λ b => if h : a = b then (@Eq.ndrec α a δ x _ h : δ b) else f _ h, λ b => _, by simp⟩
  split_ifs with h'
  · cases h'
    exact h
  · exact hf _ _

lemma image_piFinset_const [DecidableEq β] (t : Finset β) (a : α) :
    ((piFinset λ i : α => t).image λ f => f a) = t := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · haveI : Nonempty α := ⟨a⟩
    simp
  · exact image_pi_finset (λ _ => t) a λ _ _ => ht

lemma filter_piFinset_of_not_mem [∀ a, DecidableEq (δ a)] (t : ∀ a, Finset (δ a)) (a : α)
    (x : δ a) (hx : x ∉ t a) : ((piFinset t).filterₓ λ f : ∀ a, δ a => f a = x) = ∅ := by
  simp only [filter_eq_empty_iff, mem_pi_finset]; rintro f hf rfl; exact hx (hf _)

-- works better for rewrites
lemma filter_piFinset_const_of_not_mem [DecidableEq β] (t : Finset β) (a : α) (x : β)
    (hx : x ∉ t) : ((piFinset λ _ => t).filterₓ λ f : α → β => f a = x) = ∅ :=
  filter_piFinset_of_not_mem _ _ _ hx

end Fintype
