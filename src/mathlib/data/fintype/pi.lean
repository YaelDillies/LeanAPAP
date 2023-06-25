import data.finset.n_ary
import data.fintype.pi

open finset

namespace fintype
variables {α : Type*} {β γ : α → Type*} [fintype α] [decidable_eq α] [Π a, decidable_eq (γ a)]

lemma pi_finset_image (f : Π a, β a → γ a) (s : Π a, finset (β a)) :
  pi_finset (λ a, image (f a) (s a)) = image (λ (b : Π a, β a) a, f _ (b a)) (pi_finset s) :=
by ext;
  simp only [mem_pi_finset, mem_image, classical.skolem, forall_and_distrib, function.funext_iff]

end fintype

namespace fintype
variables {α : Type*} {β γ δ : α → Type*} [fintype α] [decidable_eq α] [Π a, decidable_eq (δ a)]

lemma pi_finset_image₂ (f : Π a, β a → γ a → δ a) (s : Π a, finset (β a)) (t : Π a, finset (γ a)) :
  pi_finset (λ a, image₂ (f a) (s a) (t a)) =
    image₂ (λ (b : Π a, β a) (c : Π a, γ a) a, f _ (b a) (c a)) (pi_finset s) (pi_finset t) :=
by ext;
  simp only [mem_pi_finset, mem_image₂, classical.skolem, forall_and_distrib, function.funext_iff]

end fintype
