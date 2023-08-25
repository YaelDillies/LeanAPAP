import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Data.Fintype.Card
import Mathbin.Data.IsROrC.Basic
import Mathbin.Data.Real.Nnreal
import Project.Mathlib.Algebra.BigOperators.Basic
import Project.Mathlib.Data.Pi.Algebra

#align_import mathlib.algebra.big_operators.expect

open Fintype (card)

open Function

open scoped BigOperators NNReal

variable {α β 𝕜 𝕝 : Type _}

namespace Finset

section Semifield

variable [Semifield 𝕜] [Semifield 𝕝] {s : Finset α} {t : Finset β} {f : α → 𝕜} {g : β → 𝕜}

def expect (s : Finset α) (f : α → 𝕜) : 𝕜 :=
  s.Sum f / s.card

scoped[Expectations]
  notation3"𝔼 "(...)" in "s" with "p:49:(scoped p => p)", "r:67:(scoped f =>
    Finset.expect s.filterₓ p f) => r

scoped[Expectations] notation3"𝔼 "(...)" in "s", "r:67:(scoped f => Finset.expect s f) => r

scoped[Expectations]
  notation3"𝔼 "(...)" with "p:49:(scoped p => p)", "r:67:(scoped f =>
    Finset.expect Finset.univ.filterₓ p f) => r

scoped[Expectations] notation3"𝔼 "(...)", "r:67:(scoped f => Finset.expect Finset.univ f) => r

@[simp]
theorem expect_empty (f : α → 𝕜) : expect ∅ f = 0 := by simp [expect]

@[simp]
theorem expect_singleton (f : α → 𝕜) (a : α) : expect {a} f = f a := by simp [expect]

@[simp]
theorem expect_const_zero (s : Finset α) : 𝔼 x in s, (0 : 𝕜) = 0 := by simp [expect]

theorem expect_sum_comm (s : Finset α) (t : Finset β) (f : α → β → 𝕜) :
    𝔼 x in s, ∑ y in t, f x y = ∑ y in t, 𝔼 x in s, f x y := by rw [expect, sum_comm, sum_div]; rfl

theorem expect_comm (s : Finset α) (t : Finset β) (f : α → β → 𝕜) :
    𝔼 x in s, 𝔼 y in t, f x y = 𝔼 y in t, 𝔼 x in s, f x y := by
  rw [expect, expect, ← expect_sum_comm, ← expect_sum_comm, expect, expect, div_div, mul_comm,
    div_div, sum_comm]

theorem expect_add_distrib (s : Finset α) (f g : α → 𝕜) :
    𝔼 i in s, (f i + g i) = 𝔼 i in s, f i + 𝔼 i in s, g i := by
  simp [expect, sum_add_distrib, add_div]

theorem expect_hMul (s : Finset α) (f : α → 𝕜) (x : 𝕜) : (𝔼 i in s, f i) * x = 𝔼 i in s, f i * x :=
  by rw [expect, div_mul_eq_mul_div, sum_mul]; rfl

theorem hMul_expect (s : Finset α) (f : α → 𝕜) (x : 𝕜) : x * 𝔼 i in s, f i = 𝔼 i in s, x * f i := by
  simp_rw [mul_comm x, expect_mul]

theorem expect_univ [Fintype α] : 𝔼 x, f x = (∑ x, f x) / Fintype.card α := by
  rw [expect, card_univ]

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Expectations.Mathlib.Algebra.BigOperators.Expect.«term𝔼_in_with_,_»'
theorem
  expect_congr
  ( f g : α → 𝕜 ) ( p : α → Prop ) [ DecidablePred p ] ( h : ∀ x ∈ s , p x → f x = g x )
    : 𝔼 i in s with p i , f i = 𝔼 i in s with p i , g i
  := by rw [ expect , sum_congr rfl ] · rfl simpa using h

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Expectations.Mathlib.Algebra.BigOperators.Expect.«term𝔼_in_with_,_»'
theorem
  expect_congr'
  ( f g : α → 𝕜 ) ( p : α → Prop ) [ DecidablePred p ] ( h : ∀ x , p x → f x = g x )
    : 𝔼 i in s with p i , f i = 𝔼 i in s with p i , g i
  := expect_congr _ _ _ fun x _ => h x

theorem expect_bij (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
    (i_inj : ∀ a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, b = i a ha) : 𝔼 x in s, f x = 𝔼 x in t, g x :=
  by
  rw [expect, expect, card_congr i hi i_inj, sum_bij i hi h i_inj i_surj]
  simpa [eq_comm] using i_surj

theorem expect_nbij (i : α → β) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
    (i_inj : ∀ a₁ a₂, a₁ ∈ s → a₂ ∈ s → i a₁ = i a₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ∈ s, b = i a) : 𝔼 x in s, f x = 𝔼 x in t, g x :=
  expect_bij (fun a _ => i a) hi h i_inj i_surj

theorem expect_bij' (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
    (j : ∀ a ∈ t, α) (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) : 𝔼 x in s, f x = 𝔼 x in t, g x :=
  by
  rw [expect, expect, sum_bij' i hi h j hj left_inv right_inv, card_congr i hi]
  · intro a b ha hb z
    rw [← left_inv a ha, ← left_inv b hb]
    congr 1
  intro b hb
  exact ⟨j b hb, hj _ _, right_inv _ _⟩

theorem expect_nbij' (i : α → β) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a)) (j : β → α)
    (hj : ∀ a ∈ t, j a ∈ s) (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a) :
    𝔼 x in s, f x = 𝔼 x in t, g x :=
  expect_bij' (fun a _ => i a) hi h (fun b _ => j b) hj left_inv right_inv

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem expect_product' (f : α → β → 𝕜) : 𝔼 x in s ×ˢ t, f x.1 x.2 = 𝔼 x in s, 𝔼 y in t, f x y := by
  simp only [expect, expect, card_product, sum_product', ← sum_div, div_div, mul_comm s.card,
    Nat.cast_mul]

theorem expect_multiplicative {G : Type _} [Fintype G] {f : Multiplicative G → 𝕜} :
    𝔼 x : Multiplicative G, f x = 𝔼 x, f (Multiplicative.ofAdd x) :=
  rfl

theorem map_expect {F : Type _} [RingHomClass F 𝕜 𝕝] (g : F) (f : α → 𝕜) (s : Finset α) :
    g (𝔼 x in s, f x) = 𝔼 x in s, g (f x) := by simp only [expect, map_div₀, map_natCast, map_sum]

variable [CharZero 𝕜]

@[simp]
theorem card_smul_expect (s : Finset α) (f : α → 𝕜) : s.card • 𝔼 i in s, f i = ∑ i in s, f i :=
  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [expect, nsmul_eq_mul, mul_div_cancel']
    exact Nat.cast_ne_zero.2 hs.card_pos.ne'

@[simp]
theorem card_hMul_expect (s : Finset α) (f : α → 𝕜) : ↑s.card * 𝔼 i in s, f i = ∑ i in s, f i := by
  rw [← nsmul_eq_mul, card_smul_expect]

@[simp]
theorem Fintype.card_smul_expect [Fintype α] (f : α → 𝕜) : Fintype.card α • 𝔼 i, f i = ∑ i, f i :=
  card_smul_expect _ _

@[simp]
theorem Fintype.card_hMul_expect [Fintype α] (f : α → 𝕜) :
    ↑(Fintype.card α) * 𝔼 i, f i = ∑ i, f i :=
  card_hMul_expect _ _

@[simp]
theorem expect_const (hs : s.Nonempty) (b : 𝕜) : 𝔼 i in s, b = b :=
  by
  rw [expect, sum_const, nsmul_eq_mul, mul_div_cancel_left]
  exact Nat.cast_ne_zero.2 hs.card_pos.ne'

theorem expect_indicate_eq [Fintype α] [Nonempty α] [DecidableEq α] (f : α → 𝕜) (x : α) :
    𝔼 i, ite (x = i) (Fintype.card α : 𝕜) 0 * f i = f x :=
  by
  simp_rw [expect_univ, ite_mul, MulZeroClass.zero_mul, sum_ite_eq, if_pos (mem_univ _)]
  rw [mul_div_cancel_left]
  simp [Fintype.card_ne_zero]

theorem expect_indicate_eq' [Fintype α] [Nonempty α] [DecidableEq α] (f : α → 𝕜) (x : α) :
    𝔼 i, ite (i = x) (Fintype.card α : 𝕜) 0 * f i = f x := by
  simp_rw [@eq_comm _ _ x, expect_indicate_eq]

end Semifield

open scoped Expectations

section Field

variable [Field 𝕜] [Field 𝕝] {s : Finset α}

theorem expect_sub_distrib (s : Finset α) (f g : α → 𝕜) :
    𝔼 i in s, (f i - g i) = 𝔼 i in s, f i - 𝔼 i in s, g i := by
  rw [expect, expect, expect, sum_sub_distrib, sub_div]

variable [Fintype α]

def balance (f : α → 𝕜) : α → 𝕜 :=
  f - Function.const _ (𝔼 y, f y)

theorem balance_apply (f : α → 𝕜) (x : α) : balance f x = f x - 𝔼 y, f y :=
  rfl

@[simp]
theorem balance_zero : balance (0 : α → 𝕜) = 0 := by simp [balance]

@[simp]
theorem balance_add (f g : α → 𝕜) : balance (f + g) = balance f + balance g := by
  simp only [balance, expect_add_distrib, const_add, add_sub_add_comm, Pi.add_apply]

@[simp]
theorem map_balance {F : Type _} [RingHomClass F 𝕜 𝕝] (g : F) (f : α → 𝕜) (a : α) :
    g (balance f a) = balance (g ∘ f) a := by simp [balance, map_expect]

variable [CharZero 𝕜]

@[simp]
theorem sum_balance (f : α → 𝕜) : ∑ x, balance f x = 0 := by
  cases isEmpty_or_nonempty α <;> simp [balance_apply, card_smul_expect]

@[simp]
theorem expect_balance (f : α → 𝕜) : 𝔼 x, balance f x = 0 := by simp [expect]

@[simp]
theorem balance_idem (f : α → 𝕜) : balance (balance f) = balance f := by
  cases isEmpty_or_nonempty α <;> ext x <;> simp [balance, expect_sub_distrib, univ_nonempty]

end Field

end Finset

open Finset

namespace IsROrC

variable [IsROrC 𝕜] [Fintype α] (f : α → ℝ) (a : α)

@[simp, norm_cast]
theorem coe_balance : (↑(balance f a) : 𝕜) = balance (coe ∘ f) a :=
  map_balance (algebraMap ℝ 𝕜) _ _

@[simp]
theorem coe_comp_balance : (coe : ℝ → 𝕜) ∘ balance f = balance (coe ∘ f) :=
  funext <| coe_balance _

end IsROrC

