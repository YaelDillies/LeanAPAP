import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.Card
import Mathlib.Data.IsROrC.Basic
import Mathlib.Data.Real.NNReal
import LeanAPAP.Mathlib.Algebra.BigOperators.Basic
import LeanAPAP.Mathlib.Data.Pi.Algebra

/-!
# Average over a finset

This file defines `Finset.expect`, the average (aka expectation) of a function over a finset.

## Notation

* `𝔼 i ∈ s, f i` is notation for `Finset.expect s f`. It is the expectation of `f i` where `i`
  ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
* `𝔼 x, f x` is notation for `Finset.expect Finset.univ f`. It is the expectation of `f i` where `i`
  ranges over the finite domain of `f`.
* `𝔼 i ∈ s with p i, f i` is notation for `Finset.expect (Finset.filter p s) f`. This is referred to
  as `expectWith` in lemma names.
* `𝔼 (i ∈ s) (j ∈ t), f i j` is notation for `Finset.expect (s ×ˢ t) (fun ⟨i, j⟩ ↦ f i j)`.

## Naming

We provide

-/


open Function
open Fintype (card)
open scoped NNReal

variable {ι β α 𝕝 : Type*}

namespace Finset
variable [Semifield α] [Semifield 𝕝] {s : Finset ι} {t : Finset β} {f : ι → α} {g : β → α}

/-- Average of a function over a finset. If the finset is empty, this is equal to zero. -/
def expect (s : Finset ι) (f : ι → α) : α := s.sum f / s.card

end Finset

namespace BigOps
open Std.ExtendedBinder Lean Meta

/--
* `𝔼 i ∈ s, f i` is notation for `Finset.expect s f`. It is the expectation of `f i` where `i`
  ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
* `𝔼 x, f x` is notation for `Finset.expect Finset.univ f`. It is the expectation of `f i` where `i`
  ranges over the finite domain of `f`.
* `𝔼 i ∈ s with p i, f i` is notation for `Finset.expect (Finset.filter p s) f`.
* `𝔼 (i ∈ s) (j ∈ t), f i j` is notation for `Finset.expect (s ×ˢ t) (fun ⟨i, j⟩ ↦ f i j)`.

These support destructuring, for example `𝔼 ⟨i, j⟩ ∈ s ×ˢ t, f i j`.

Notation: `"𝔼" bigOpBinders* ("with" term)? "," term` -/
scoped syntax (name := bigexpect) "𝔼 " bigOpBinders ("with " term)? ", " term:67 : term

scoped macro_rules (kind := bigexpect)
  | `(𝔼 $bs:bigOpBinders $[with $p?]?, $v) => do
    let processed ← processBigOpBinders bs
    let x ← bigOpBindersPattern processed
    let s ← bigOpBindersProd processed
    match p? with
    | some p => `(Finset.expect (Finset.filter (fun $x ↦ $p) $s) (fun $x ↦ $v))
    | none => `(Finset.expect $s (fun $x ↦ $v))

open Lean Meta Parser.Term PrettyPrinter.Delaborator SubExpr
open Std.ExtendedBinder

/-- Delaborator for `Finset.expect`. The `pp.piBinderTypes` option controls whether
to show the domain type when the expect is over `Finset.univ`. -/
@[scoped delab app.Finset.expect] def delabFinsetexpect : Delab := whenPPOption getPPNotation do
  let #[_, _, _, s, f] := (← getExpr).getAppArgs | failure
  guard $ f.isLambda
  let ppDomain ← getPPOption getPPPiBinderTypes
  let (i, body) ← withAppArg $ withBindingBodyUnusedName fun i => do
    return (i, ← delab)
  if s.isAppOfArity ``Finset.univ 2 then
    let binder ←
      if ppDomain then
        let ty ← withNaryArg 0 delab
        `(bigOpBinder| $(.mk i):ident : $ty)
      else
        `(bigOpBinder| $(.mk i):ident)
    `(𝔼 $binder:bigOpBinder, $body)
  else
    let ss ← withNaryArg 3 $ delab
    `(𝔼 $(.mk i):ident ∈ $ss, $body)

end BigOps

open scoped BigOps

namespace Finset
section Semifield
variable [Semifield α] [Semifield 𝕝] {s : Finset ι} {t : Finset β} {f : ι → α} {g : β → α}

@[simp] lemma expect_empty (f : ι → α) : expect ∅ f = 0 := by simp [expect]
@[simp] lemma expect_singleton (f : ι → α) (a : ι) : expect {a} f = f a := by simp [expect]
@[simp] lemma expect_const_zero (s : Finset ι) : 𝔼 _x ∈ s, (0 : α) = 0 := by simp [expect]

lemma expect_sum_comm (s : Finset ι) (t : Finset β) (f : ι → β → α) :
    𝔼 x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, 𝔼 x ∈ s, f x y := by rw [expect, sum_comm, sum_div]; rfl

lemma expect_comm (s : Finset ι) (t : Finset β) (f : ι → β → α) :
    𝔼 x ∈ s, 𝔼 y ∈ t, f x y = 𝔼 y ∈ t, 𝔼 x ∈ s, f x y := by
  rw [expect, expect, ←expect_sum_comm, ←expect_sum_comm, expect, expect, div_div, mul_comm,
    div_div, sum_comm]

lemma expect_add_distrib (s : Finset ι) (f g : ι → α) :
    𝔼 i ∈ s, (f i + g i) = 𝔼 i ∈ s, f i + 𝔼 i ∈ s, g i := by
  simp [expect, sum_add_distrib, add_div]

lemma expect_mul (s : Finset ι) (f : ι → α) (a : α) : (𝔼 i ∈ s, f i) * a = 𝔼 i ∈ s, f i * a := by
  rw [expect, div_mul_eq_mul_div, sum_mul]; rfl

lemma mul_expect (s : Finset ι) (f : ι → α) (a : α) : a * 𝔼 i ∈ s, f i = 𝔼 i ∈ s, a * f i := by
  simp_rw [mul_comm a, expect_mul]

lemma expect_div (s : Finset ι) (f : ι → α) (a : α) : (𝔼 i ∈ s, f i) / a = 𝔼 i ∈ s, f i / a := by
  simp_rw [div_eq_mul_inv, expect_mul]

lemma expect_univ [Fintype ι] : 𝔼 x, f x = (∑ x, f x) / Fintype.card ι := by
  rw [expect, card_univ]

lemma expect_congr (f g : ι → α) (h : ∀ x ∈ s, f x = g x) : 𝔼 i ∈ s, f i = 𝔼 i ∈ s, g i := by
   rw [expect, expect, sum_congr rfl h]

lemma expectWith_congr (f g : ι → α) (p : ι → Prop) [DecidablePred p]
    (h : ∀ x ∈ s, p x → f x = g x) : 𝔼 i ∈ s with p i, f i = 𝔼 i ∈ s with p i, g i :=
  expect_congr _ _ $ by simpa using h

lemma expect_bij (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
    (i_inj : ∀ a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, b = i a ha) : 𝔼 x ∈ s, f x = 𝔼 x ∈ t, g x := by
  rw [expect, expect, card_congr i hi i_inj, sum_bij i hi h i_inj i_surj]
  simpa [eq_comm] using i_surj

lemma expect_nbij (i : ι → β) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
    (i_inj : ∀ a₁ a₂, a₁ ∈ s → a₂ ∈ s → i a₁ = i a₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ∈ s, b = i a) : 𝔼 x ∈ s, f x = 𝔼 x ∈ t, g x :=
  expect_bij (fun a _ ↦ i a) hi h i_inj $ by simpa using i_surj

lemma expect_bij' (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
    (j : ∀ a ∈ t, ι) (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) : 𝔼 x ∈ s, f x = 𝔼 x ∈ t, g x := by
  rw [expect, expect, sum_bij' i hi h j hj left_inv right_inv, card_congr i hi]
  · intro a b ha hb z
    rw [←left_inv a ha, ←left_inv b hb]
    congr 1
  intro b hb
  exact ⟨j b hb, hj _ _, right_inv _ _⟩

lemma expect_nbij' (i : ι → β) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a)) (j : β → ι)
    (hj : ∀ a ∈ t, j a ∈ s) (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a) :
    𝔼 x ∈ s, f x = 𝔼 x ∈ t, g x :=
  expect_bij' (fun a _ ↦ i a) hi h (fun b _ ↦ j b) hj left_inv right_inv

lemma expect_product' (f : ι → β → α) : 𝔼 x ∈ s ×ˢ t, f x.1 x.2 = 𝔼 x ∈ s, 𝔼 y ∈ t, f x y := by
  simp only [expect, expect, card_product, sum_product', ←sum_div, div_div, mul_comm s.card,
    Nat.cast_mul]

lemma map_expect {F : Type*} [RingHomClass F α 𝕝] (g : F) (f : ι → α) (s : Finset ι) :
    g (𝔼 x ∈ s, f x) = 𝔼 x ∈ s, g (f x) := by simp only [expect, map_div₀, map_natCast, map_sum]

variable [CharZero α]

@[simp]
lemma card_smul_expect (s : Finset ι) (f : ι → α) : s.card • 𝔼 i ∈ s, f i = ∑ i ∈ s, f i := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [expect, nsmul_eq_mul, mul_div_cancel']
    exact Nat.cast_ne_zero.2 hs.card_pos.ne'

@[simp] lemma card_mul_expect (s : Finset ι) (f : ι → α) :
    s.card * 𝔼 i ∈ s, f i = ∑ i ∈ s, f i := by rw [←nsmul_eq_mul, card_smul_expect]

@[simp] nonrec lemma Fintype.card_smul_expect [Fintype ι] (f : ι → α) :
    Fintype.card ι • 𝔼 i, f i = ∑ i, f i := card_smul_expect _ _

@[simp] nonrec lemma Fintype.card_mul_expect [Fintype ι] (f : ι → α) :
    ↑(Fintype.card ι) * 𝔼 i, f i = ∑ i, f i :=
  card_mul_expect _ _

@[simp]
lemma expect_const (hs : s.Nonempty) (b : α) : 𝔼 _i ∈ s, b = b := by
  rw [expect, sum_const, nsmul_eq_mul, mul_div_cancel_left]
  exact Nat.cast_ne_zero.2 hs.card_pos.ne'

lemma expect_indicate_eq [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι → α) (x : ι) :
    𝔼 i, ite (x = i) (Fintype.card ι : α) 0 * f i = f x := by
  simp_rw [expect_univ, ite_mul, MulZeroClass.zero_mul, sum_ite_eq, if_pos (mem_univ _)]
  rw [mul_div_cancel_left]
  simp [Fintype.card_ne_zero]

lemma expect_indicate_eq' [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι → α) (x : ι) :
    𝔼 i, ite (i = x) (Fintype.card ι : α) 0 * f i = f x := by
  simp_rw [@eq_comm _ _ x, expect_indicate_eq]

end Semifield

section Field
variable [Field α] [Field 𝕝] {s : Finset ι}

lemma expect_sub_distrib (s : Finset ι) (f g : ι → α) :
    𝔼 i ∈ s, (f i - g i) = 𝔼 i ∈ s, f i - 𝔼 i ∈ s, g i := by
  rw [expect, expect, expect, sum_sub_distrib, sub_div]

variable [Fintype ι]

def balance (f : ι → α) : ι → α := f - Function.const _ (𝔼 y, f y)

lemma balance_apply (f : ι → α) (x : ι) : balance f x = f x - 𝔼 y, f y := rfl

@[simp] lemma balance_zero : balance (0 : ι → α) = 0 := by simp [balance]

@[simp] lemma balance_add (f g : ι → α) : balance (f + g) = balance f + balance g := by
  simp only [balance, expect_add_distrib, const_add, add_sub_add_comm, Pi.add_apply]

@[simp]
lemma map_balance {F : Type*} [RingHomClass F α 𝕝] (g : F) (f : ι → α) (a : ι) :
    g (balance f a) = balance (g ∘ f) a := by simp [balance, map_expect]

variable [CharZero α]

@[simp]
lemma sum_balance (f : ι → α) : ∑ x, balance f x = 0 := by
  cases isEmpty_or_nonempty ι <;> simp [balance_apply, card_smul_expect]

@[simp]
lemma expect_balance (f : ι → α) : 𝔼 x, balance f x = 0 := by simp [expect]

@[simp]
lemma balance_idem (f : ι → α) : balance (balance f) = balance f := by
  cases isEmpty_or_nonempty ι <;> ext x <;> simp [balance, expect_sub_distrib, univ_nonempty]

end Field

section LinearOrderedSemifield
variable [LinearOrderedSemifield α] {s : Finset ι} {f g : ι → α}

lemma expect_le_expect (hfg : ∀ i ∈ s, f i ≤ g i) : 𝔼 i ∈ s, f i ≤ 𝔼 i ∈ s, g i :=
  div_le_div_of_le (by positivity) $ sum_le_sum hfg

lemma expect_le (hs : s.Nonempty) (f : ι → α) (a : α) (h : ∀ x ∈ s, f x ≤ a) : 𝔼 i ∈ s, f i ≤ a :=
  (div_le_iff' $ Nat.cast_pos.2 hs.card_pos).2 $ by
    rw [←nsmul_eq_mul]; exact sum_le_card_nsmul _ _ _ h

lemma le_expect (hs : s.Nonempty) (f : ι → α) (a : α) (h : ∀ x ∈ s, a ≤ f x) : a ≤ 𝔼 i ∈ s, f i :=
  (le_div_iff' $ Nat.cast_pos.2 hs.card_pos).2 $ by
    rw [←nsmul_eq_mul]; exact card_nsmul_le_sum _ _ _ h

end LinearOrderedSemifield
end Finset

open Finset

namespace IsROrC
variable [IsROrC α] [Fintype ι] (f : ι → ℝ) (a : ι)

@[simp, norm_cast]
lemma coe_balance : (↑(balance f a) : α) = balance ((↑) ∘ f) a := map_balance (algebraMap ℝ α) _ _

@[simp] lemma coe_comp_balance : ((↑) : ℝ → α) ∘ balance f = balance ((↑) ∘ f) :=
  funext $ coe_balance _

end IsROrC
