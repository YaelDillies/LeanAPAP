import algebra.big_operators.ring
import data.fintype.card
import mathlib.algebra.big_operators.basic

open fintype (card)
open_locale big_operators

variables {α β 𝕜 𝕝 : Type*}

namespace finset
section semifield
variables [semifield 𝕜] [semifield 𝕝] {s : finset α} {t : finset β} {f : α → 𝕜} {g : β → 𝕜}

def expect (s : finset α) (f : α → 𝕜) : 𝕜 := s.sum f / s.card

localized "notation `𝔼` binders ` in ` s ` with ` p:(scoped:49 p, p) `, ` r:(scoped:67 f, finset.expect (s.filter p) f) := r" in expectations
localized "notation `𝔼` binders ` in ` s `, ` r:(scoped:67 f, finset.expect s f) := r" in expectations
localized "notation `𝔼` binders ` with ` p:(scoped:49 p, p) `, ` r:(scoped:67 f, finset.expect (finset.univ.filter p) f) := r" in expectations
localized "notation `𝔼` binders `, ` r:(scoped:67 f, finset.expect finset.univ f) := r" in expectations

@[simp] lemma expect_empty (f : α → 𝕜) : expect ∅ f = 0 := by simp [expect]
@[simp] lemma expect_singleton (f : α → 𝕜) (a : α) : expect {a} f = f a := by simp [expect]

lemma expect_sum_comm (s : finset α) (t : finset β) (f : α → β → 𝕜) :
  𝔼 x in s, ∑ y in t, f x y = ∑ y in t, 𝔼 x in s, f x y :=
by { rw [expect, sum_comm, sum_div], refl }

lemma expect_comm (s : finset α) (t : finset β) (f : α → β → 𝕜) :
  𝔼 x in s, 𝔼 y in t, f x y = 𝔼 y in t, 𝔼 x in s, f x y :=
by rw [expect, expect, ←expect_sum_comm, ←expect_sum_comm, expect, expect, div_div, mul_comm,
  div_div, sum_comm]

lemma expect_mul (s : finset α) (f : α → 𝕜) (x : 𝕜) : (𝔼 i in s, f i) * x = 𝔼 i in s, f i * x :=
by { rw [expect, div_mul_eq_mul_div, sum_mul], refl }

lemma mul_expect (s : finset α) (f : α → 𝕜) (x : 𝕜) : x * 𝔼 i in s, f i = 𝔼 i in s, x * f i :=
by simp_rw [mul_comm x, expect_mul]

lemma expect_univ [fintype α] : 𝔼 x, f x = (∑ x, f x) / fintype.card α :=
by rw [expect, card_univ]

lemma expect_congr (f g : α → 𝕜) (p : α → Prop) [decidable_pred p] (h : ∀ x ∈ s, p x → f x = g x) :
  𝔼 i in s with p i, f i = 𝔼 i in s with p i, g i :=
begin
  rw [expect, sum_congr rfl],
  { refl },
  simpa using h
end

lemma expect_congr' (f g : α → 𝕜) (p : α → Prop) [decidable_pred p] (h : ∀ x, p x → f x = g x) :
  𝔼 i in s with p i, f i = 𝔼 i in s with p i, g i :=
expect_congr _ _ _ (λ x _, h x)

lemma expect_bij (i : Π a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
  (i_inj : ∀ a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂) (i_surj : ∀ b ∈ t, ∃ a ha, b = i a ha) :
  𝔼 x in s, f x = 𝔼 x in t, g x :=
begin
  rw [expect, expect, card_congr i hi i_inj, sum_bij i hi h i_inj i_surj],
  simpa [eq_comm] using i_surj,
end

lemma expect_nbij (i : α → β) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
  (i_inj : ∀ a₁ a₂, a₁ ∈ s → a₂ ∈ s → i a₁ = i a₂ → a₁ = a₂) (i_surj : ∀ b ∈ t, ∃ a ∈ s, b = i a) :
  𝔼 x in s, f x = 𝔼 x in t, g x :=
expect_bij (λ a _, i a) hi h i_inj i_surj

lemma expect_bij' (i : Π a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t)
  (h : ∀ a ha, f a = g (i a ha)) (j : Π a ∈ t, α) (hj : ∀ a ha, j a ha ∈ s)
  (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a) (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) :
  𝔼 x in s, f x = 𝔼 x in t, g x :=
begin
  rw [expect, expect, sum_bij' i hi h j hj left_inv right_inv, card_congr i hi],
  { intros a b ha hb z,
    rw [←left_inv a ha, ←left_inv b hb],
    congr' 1 },
  intros b hb,
  exact ⟨j b hb, hj _ _, right_inv _ _⟩,
end

lemma expect_nbij' (i : α → β) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a)) (j : β → α)
  (hj : ∀ a ∈ t, j a ∈ s) (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a) :
  𝔼 x in s, f x = 𝔼 x in t, g x :=
expect_bij' (λ a _, i a) hi h (λ b _, j b) hj left_inv right_inv

lemma expect_product' (f : α → β → 𝕜) : 𝔼 x in s ×ˢ t, f x.1 x.2 = 𝔼 x in s, 𝔼 y in t, f x y :=
by simp only [expect, expect, card_product, sum_product', ←sum_div, div_div, mul_comm s.card,
    nat.cast_mul]

lemma expect_multiplicative {G : Type*} [fintype G] {f : multiplicative G → 𝕜} :
  𝔼 x : multiplicative G, f x = 𝔼 x, f (multiplicative.of_add x) := rfl

lemma map_expect {F : Type*} [ring_hom_class F 𝕜 𝕝] (g : F) (f : α → 𝕜) (s : finset α) :
  g (𝔼 x in s, f x) = 𝔼 x in s, g (f x) :=
by simp only [expect, map_div₀, map_nat_cast, map_sum]

variables [char_zero 𝕜]

lemma expect_const (hs : s.nonempty) (b : 𝕜) : 𝔼 i in s, b = b :=
begin
  rw [expect, sum_const, nsmul_eq_mul, mul_div_cancel_left],
  exact nat.cast_ne_zero.2 hs.card_pos.ne',
end

lemma expect_indicate_eq [fintype α] [nonempty α] [decidable_eq α]
  (f : α → 𝕜) (x : α) : 𝔼 i, ite (x = i) (fintype.card α : 𝕜) 0 * f i = f x :=
begin
  simp_rw [expect_univ, ite_mul, zero_mul, sum_ite_eq, if_pos (mem_univ _)],
  rw mul_div_cancel_left,
  simp [fintype.card_ne_zero],
end

lemma expect_indicate_eq' [fintype α] [nonempty α] [decidable_eq α]
  (f : α → 𝕜) (x : α) : 𝔼 i, ite (i = x) (fintype.card α : 𝕜) 0 * f i = f x :=
by simp_rw [@eq_comm _ _ x, expect_indicate_eq]

end semifield

open_locale expectations

section field
variables [field 𝕜] {s : finset α}

lemma expect_sub (s : finset α) (f g : α → 𝕜) :
  𝔼 i in s, (f i - g i) = 𝔼 i in s, f i - 𝔼 i in s, g i :=
by rw [expect, expect, expect, sum_sub_distrib, sub_div]

variables [fintype α]

def balance (f : α → 𝕜) (x : α) : 𝕜 := f x - 𝔼 y, f y

lemma expect_balance [char_zero 𝕜] (f : α → 𝕜) : 𝔼 x, balance f x = 0 :=
begin
  casesI is_empty_or_nonempty α,
  { simp },
  { simp only [balance, expect_sub, expect_const univ_nonempty, sub_self] }
end

end field
end finset
