import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.Card
import Mathlib.Data.IsROrC.Basic
import Mathlib.Data.Real.NNReal
import LeanAPAP.Mathlib.Algebra.BigOperators.Basic
import LeanAPAP.Mathlib.Data.Pi.Algebra


open Function
open Fintype (card)
open scoped NNReal

variable {α β 𝕜 𝕝 : Type*}

namespace Finset
variable [Semifield 𝕜] [Semifield 𝕝] {s : Finset α} {t : Finset β} {f : α → 𝕜} {g : β → 𝕜}

def expect (s : Finset α) (f : α → 𝕜) : 𝕜 := s.sum f / s.card

end Finset

namespace BigOps
open Std.ExtendedBinder Lean Meta

/--
- `𝔼 x, f x` is notation for `Finset.expect Finset.univ f`. It is the expect of `f x`,
  where `x` ranges over the finite domain of `f`.
- `𝔼 x ∈ s, f x` is notation for `Finset.expect s f`. It is the expect of `f x`,
  where `x` ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
- `𝔼 x ∈ s with p x, f x` is notation for `Finset.expect (Finset.filter p s) f`.
- `𝔼 (x ∈ s) (y ∈ t), f x y` is notation for `Finset.expect (s ×ˢ t) (fun ⟨x, y⟩ ↦ f x y)`.

These support destructuring, for example `𝔼 ⟨x, y⟩ ∈ s ×ˢ t, f x y`.

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
variable [Semifield 𝕜] [Semifield 𝕝] {s : Finset α} {t : Finset β} {f : α → 𝕜} {g : β → 𝕜}

@[simp] lemma expect_empty (f : α → 𝕜) : expect ∅ f = 0 := by simp [expect]
@[simp] lemma expect_singleton (f : α → 𝕜) (a : α) : expect {a} f = f a := by simp [expect]
@[simp] lemma expect_const_zero (s : Finset α) : 𝔼 _x ∈ s, (0 : 𝕜) = 0 := by simp [expect]

lemma expect_sum_comm (s : Finset α) (t : Finset β) (f : α → β → 𝕜) :
    𝔼 x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, 𝔼 x ∈ s, f x y := by rw [expect, sum_comm, sum_div]; rfl

lemma expect_comm (s : Finset α) (t : Finset β) (f : α → β → 𝕜) :
    𝔼 x ∈ s, 𝔼 y ∈ t, f x y = 𝔼 y ∈ t, 𝔼 x ∈ s, f x y := by
  rw [expect, expect, ←expect_sum_comm, ←expect_sum_comm, expect, expect, div_div, mul_comm,
    div_div, sum_comm]

lemma expect_add_distrib (s : Finset α) (f g : α → 𝕜) :
    𝔼 i ∈ s, (f i + g i) = 𝔼 i ∈ s, f i + 𝔼 i ∈ s, g i := by
  simp [expect, sum_add_distrib, add_div]

lemma expect_mul (s : Finset α) (f : α → 𝕜) (x : 𝕜) : (𝔼 i ∈ s, f i) * x = 𝔼 i ∈ s, f i * x := by
  rw [expect, div_mul_eq_mul_div, sum_mul]; rfl

lemma mul_expect (s : Finset α) (f : α → 𝕜) (x : 𝕜) : x * 𝔼 i ∈ s, f i = 𝔼 i ∈ s, x * f i := by
  simp_rw [mul_comm x, expect_mul]

lemma expect_univ [Fintype α] : 𝔼 x, f x = (∑ x, f x) / Fintype.card α := by
  rw [expect, card_univ]

lemma expect_congr (f g : α → 𝕜) (p : α → Prop) [DecidablePred p] (h : ∀ x ∈ s, p x → f x = g x) :
    𝔼 i ∈ s with p i, f i = 𝔼 i ∈ s with p i, g i := by
  rw [expect, expect, sum_congr rfl]; simpa using h

lemma expect_congr' (f g : α → 𝕜) (p : α → Prop) [DecidablePred p] (h : ∀ x, p x → f x = g x) :
    𝔼 i ∈ s with p i, f i = 𝔼 i ∈ s with p i, g i := expect_congr _ _ _ λ x _ ↦ h x

lemma expect_bij (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
    (i_inj : ∀ a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, b = i a ha) : 𝔼 x ∈ s, f x = 𝔼 x ∈ t, g x := by
  rw [expect, expect, card_congr i hi i_inj, sum_bij i hi h i_inj i_surj]
  simpa [eq_comm] using i_surj

lemma expect_nbij (i : α → β) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
    (i_inj : ∀ a₁ a₂, a₁ ∈ s → a₂ ∈ s → i a₁ = i a₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ∈ s, b = i a) : 𝔼 x ∈ s, f x = 𝔼 x ∈ t, g x :=
  expect_bij (λ a _ ↦ i a) hi h i_inj $ by simpa using i_surj

lemma expect_bij' (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
    (j : ∀ a ∈ t, α) (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) : 𝔼 x ∈ s, f x = 𝔼 x ∈ t, g x := by
  rw [expect, expect, sum_bij' i hi h j hj left_inv right_inv, card_congr i hi]
  · intro a b ha hb z
    rw [←left_inv a ha, ←left_inv b hb]
    congr 1
  intro b hb
  exact ⟨j b hb, hj _ _, right_inv _ _⟩

lemma expect_nbij' (i : α → β) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a)) (j : β → α)
    (hj : ∀ a ∈ t, j a ∈ s) (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a) :
    𝔼 x ∈ s, f x = 𝔼 x ∈ t, g x :=
  expect_bij' (λ a _ ↦ i a) hi h (λ b _ ↦ j b) hj left_inv right_inv

lemma expect_product' (f : α → β → 𝕜) : 𝔼 x ∈ s ×ˢ t, f x.1 x.2 = 𝔼 x ∈ s, 𝔼 y ∈ t, f x y := by
  simp only [expect, expect, card_product, sum_product', ←sum_div, div_div, mul_comm s.card,
    Nat.cast_mul]

lemma map_expect {F : Type*} [RingHomClass F 𝕜 𝕝] (g : F) (f : α → 𝕜) (s : Finset α) :
    g (𝔼 x ∈ s, f x) = 𝔼 x ∈ s, g (f x) := by simp only [expect, map_div₀, map_natCast, map_sum]

variable [CharZero 𝕜]

@[simp]
lemma card_smul_expect (s : Finset α) (f : α → 𝕜) : s.card • 𝔼 i ∈ s, f i = ∑ i ∈ s, f i := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [expect, nsmul_eq_mul, mul_div_cancel']
    exact Nat.cast_ne_zero.2 hs.card_pos.ne'

@[simp] lemma card_mul_expect (s : Finset α) (f : α → 𝕜) :
    s.card * 𝔼 i ∈ s, f i = ∑ i ∈ s, f i := by rw [←nsmul_eq_mul, card_smul_expect]

@[simp] nonrec lemma Fintype.card_smul_expect [Fintype α] (f : α → 𝕜) :
    Fintype.card α • 𝔼 i, f i = ∑ i, f i := card_smul_expect _ _

@[simp] nonrec lemma Fintype.card_mul_expect [Fintype α] (f : α → 𝕜) :
    ↑(Fintype.card α) * 𝔼 i, f i = ∑ i, f i :=
  card_mul_expect _ _

@[simp]
lemma expect_const (hs : s.Nonempty) (b : 𝕜) : 𝔼 _i ∈ s, b = b := by
  rw [expect, sum_const, nsmul_eq_mul, mul_div_cancel_left]
  exact Nat.cast_ne_zero.2 hs.card_pos.ne'

lemma expect_indicate_eq [Fintype α] [Nonempty α] [DecidableEq α] (f : α → 𝕜) (x : α) :
    𝔼 i, ite (x = i) (Fintype.card α : 𝕜) 0 * f i = f x := by
  simp_rw [expect_univ, ite_mul, MulZeroClass.zero_mul, sum_ite_eq, if_pos (mem_univ _)]
  rw [mul_div_cancel_left]
  simp [Fintype.card_ne_zero]

lemma expect_indicate_eq' [Fintype α] [Nonempty α] [DecidableEq α] (f : α → 𝕜) (x : α) :
    𝔼 i, ite (i = x) (Fintype.card α : 𝕜) 0 * f i = f x := by
  simp_rw [@eq_comm _ _ x, expect_indicate_eq]

end Semifield

section Field
variable [Field 𝕜] [Field 𝕝] {s : Finset α}

lemma expect_sub_distrib (s : Finset α) (f g : α → 𝕜) :
    𝔼 i ∈ s, (f i - g i) = 𝔼 i ∈ s, f i - 𝔼 i ∈ s, g i := by
  rw [expect, expect, expect, sum_sub_distrib, sub_div]

variable [Fintype α]

def balance (f : α → 𝕜) : α → 𝕜 := f - Function.const _ (𝔼 y, f y)

lemma balance_apply (f : α → 𝕜) (x : α) : balance f x = f x - 𝔼 y, f y := rfl

@[simp] lemma balance_zero : balance (0 : α → 𝕜) = 0 := by simp [balance]

@[simp] lemma balance_add (f g : α → 𝕜) : balance (f + g) = balance f + balance g := by
  simp only [balance, expect_add_distrib, const_add, add_sub_add_comm, Pi.add_apply]

@[simp]
lemma map_balance {F : Type*} [RingHomClass F 𝕜 𝕝] (g : F) (f : α → 𝕜) (a : α) :
    g (balance f a) = balance (g ∘ f) a := by simp [balance, map_expect]

variable [CharZero 𝕜]

@[simp]
lemma sum_balance (f : α → 𝕜) : ∑ x, balance f x = 0 := by
  cases isEmpty_or_nonempty α <;> simp [balance_apply, card_smul_expect]

@[simp]
lemma expect_balance (f : α → 𝕜) : 𝔼 x, balance f x = 0 := by simp [expect]

@[simp]
lemma balance_idem (f : α → 𝕜) : balance (balance f) = balance f := by
  cases isEmpty_or_nonempty α <;> ext x <;> simp [balance, expect_sub_distrib, univ_nonempty]

end Field

end Finset

open Finset

namespace IsROrC
variable [IsROrC 𝕜] [Fintype α] (f : α → ℝ) (a : α)

@[simp, norm_cast]
lemma coe_balance : (↑(balance f a) : 𝕜) = balance ((↑) ∘ f) a := map_balance (algebraMap ℝ 𝕜) _ _

@[simp] lemma coe_comp_balance : ((↑) : ℝ → 𝕜) ∘ balance f = balance ((↑) ∘ f) :=
  funext $ coe_balance _

end IsROrC
