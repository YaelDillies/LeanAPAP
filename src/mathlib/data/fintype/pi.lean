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

namespace fintype
variables {α β : Type*} {δ : α → Type*}

@[reducible] def pi_finset_const (s : finset α) (n : ℕ) := pi_finset $ λ _ : fin n, s

infix `^^`:70 := pi_finset_const

variables [decidable_eq α] [fintype α]

lemma image_pi_finset (t : Π a, finset (δ a)) (a : α) [decidable_eq (δ a)]
  (ht : ∀ b, a ≠ b → (t b).nonempty) :
  (pi_finset t).image (λ f, f a) = t a :=
begin
  ext x,
  simp only [mem_image, mem_pi_finset, exists_prop],
  split,
  { rintro ⟨f, hf, rfl⟩,
    exact hf _ },
  intro h,
  choose f hf using ht,
  refine ⟨λ b, if h : a = b then ((@eq.rec α a δ x _ h) : δ b) else f _ h, λ b, _, by simp⟩,
  split_ifs with h',
  { cases h',
    exact h },
  { exact hf _ _ }
end

lemma image_pi_finset_const [decidable_eq β] (t : finset β) (a : α) :
  (pi_finset (λ i : α, t)).image (λ f, f a) = t :=
begin
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { haveI : nonempty α := ⟨a⟩,
    simp },
  { exact image_pi_finset (λ _, t) a (λ _ _, ht) }
end

lemma filter_pi_finset_of_not_mem [Π a, decidable_eq (δ a)] (t : Π a, finset (δ a)) (a : α)
  (x : δ a) (hx : x ∉ t a) :
  (pi_finset t).filter (λ f : Π a, δ a, f a = x) = ∅ :=
by { simp only [filter_eq_empty_iff, mem_pi_finset], rintro f hf rfl, exact hx (hf _) }

-- works better for rewrites
lemma filter_pi_finset_const_of_not_mem [decidable_eq β] (t : finset β) (a : α) (x : β)
  (hx : x ∉ t) : (pi_finset (λ _, t)).filter (λ f : α → β, f a = x) = ∅ :=
filter_pi_finset_of_not_mem _ _ _ hx

end fintype
