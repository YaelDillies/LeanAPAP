import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.Card
import Mathlib.Data.IsROrC.Basic
import Mathlib.Data.Real.NNReal
import LeanAPAP.Mathlib.Algebra.BigOperators.Basic
import LeanAPAP.Mathlib.Algebra.BigOperators.Order
import LeanAPAP.Mathlib.Algebra.Order.Field.Basic
import LeanAPAP.Mathlib.Data.Pi.Algebra
import LeanAPAP.Mathlib.Tactic.Positivity.Finset

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
-/

section
variable {α β : Type*}

/-- Note that the `IsScalarTower α β β` typeclass argument is usually satisfied by `Algebra α β`.
-/
@[to_additive]
lemma smul_div_assoc [DivInvMonoid β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β) :
    r • x / y = r • (x / y) := by simp [div_eq_mul_inv, smul_mul_assoc]

end


open Function
open Fintype (card)
open scoped NNReal

variable {ι κ β α 𝕝 : Type*}

/-- Average of a function over a finset. If the finset is empty, this is equal to zero. -/
def Finset.expect [Semifield α] (s : Finset ι) (f : ι → α) : α := s.sum f / s.card

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
variable [Semifield α] [Semifield 𝕝] {s : Finset ι} {f g : ι → α} {m : β → α}

lemma expect_univ [Fintype ι] : 𝔼 x, f x = (∑ x, f x) / Fintype.card ι := by
  rw [expect, card_univ]

@[simp] lemma expect_empty (f : ι → α) : expect ∅ f = 0 := by simp [expect]
@[simp] lemma expect_singleton (f : ι → α) (i : ι) : expect {i} f = f i := by simp [expect]
@[simp] lemma expect_const_zero (s : Finset ι) : 𝔼 _i ∈ s, (0 : α) = 0 := by simp [expect]

@[congr]
lemma expect_congr {t : Finset ι} (hst : s = t) (h : ∀ x ∈ t, f x = g x) :
    𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by rw [expect, expect, sum_congr hst h, hst]

lemma expectWith_congr (p : ι → Prop) [DecidablePred p] (h : ∀ x ∈ s, p x → f x = g x) :
    𝔼 i ∈ s with p i, f i = 𝔼 i ∈ s with p i, g i :=
  expect_congr rfl $ by simpa using h

lemma expect_sum_comm (s : Finset ι) (t : Finset β) (f : ι → β → α) :
    𝔼 x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, 𝔼 x ∈ s, f x y := by rw [expect, sum_comm, sum_div]; rfl

lemma expect_comm (s : Finset ι) (t : Finset β) (f : ι → β → α) :
    𝔼 x ∈ s, 𝔼 y ∈ t, f x y = 𝔼 y ∈ t, 𝔼 x ∈ s, f x y := by
  rw [expect, expect, ←expect_sum_comm, ←expect_sum_comm, expect, expect, div_div, mul_comm,
    div_div, sum_comm]

lemma expect_eq_zero (h : ∀ i ∈ s, f i = 0) : 𝔼 i ∈ s, f i = 0 :=
  (expect_congr rfl h).trans s.expect_const_zero

-- TODO: Golf `exists_ne_zero_of_sum_ne_zero`
lemma exists_ne_zero_of_expect_ne_zero (h : 𝔼 i ∈ s, f i ≠ 0) : ∃ i ∈ s, f i ≠ 0 := by
  contrapose! h; exact expect_eq_zero h

lemma expect_add_distrib (s : Finset ι) (f g : ι → α) :
    𝔼 i ∈ s, (f i + g i) = 𝔼 i ∈ s, f i + 𝔼 i ∈ s, g i := by
  simp [expect, sum_add_distrib, add_div]

lemma expect_add_expect_comm (f₁ f₂ g₁ g₂ : ι → α) :
    𝔼 i ∈ s, (f₁ i + f₂ i) + 𝔼 i ∈ s, (g₁ i + g₂ i) =
      𝔼 i ∈ s, (f₁ i + g₁ i) + 𝔼 i ∈ s, (f₂ i + g₂ i) := by
  simp_rw [expect_add_distrib, add_add_add_comm]

lemma expect_mul (s : Finset ι) (f : ι → α) (a : α) : (𝔼 i ∈ s, f i) * a = 𝔼 i ∈ s, f i * a := by
  rw [expect, div_mul_eq_mul_div, sum_mul]; rfl

lemma mul_expect (s : Finset ι) (f : ι → α) (a : α) : a * 𝔼 i ∈ s, f i = 𝔼 i ∈ s, a * f i := by
  simp_rw [mul_comm a, expect_mul]

lemma expect_div (s : Finset ι) (f : ι → α) (a : α) : (𝔼 i ∈ s, f i) / a = 𝔼 i ∈ s, f i / a := by
  simp_rw [div_eq_mul_inv, expect_mul]

-- TODO: Change `sum_mul_sum` to match?
lemma expect_mul_expect (s : Finset ι) (t : Finset κ) (f : ι → α) (g : κ → α) :
    (𝔼 i ∈ s, f i) * 𝔼 j ∈ t, g j = 𝔼 i ∈ s, 𝔼 j ∈ t, f i * g j := by
  simp_rw [expect_mul, mul_expect]

lemma expect_eq_single_of_mem (i : ι) (hi : i ∈ s) (h : ∀ j ∈ s, j ≠ i → f j = 0) :
    𝔼 i ∈ s, f i = f i / s.card := by rw [expect, sum_eq_single_of_mem _ hi h]

/-- See also `Finset.expect_boole`. -/
lemma expect_ite_zero (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    (h : ∀ i ∈ s, ∀ j ∈ s, p i → p j → i = j) (a : α) :
    𝔼 i ∈ s, ite (p i) a 0 = ite (∃ i ∈ s, p i) (a / s.card) 0 := by
  split_ifs <;> simp [expect, sum_ite_zero' _ _ h, *]

section DecidableEq
variable [DecidableEq ι]

@[simp] lemma expect_dite_eq (i : ι) (f : ∀ j, i = j → α) :
    𝔼 j ∈ s, (if h : i = j then f j h else 0) = if i ∈ s then f i rfl / s.card else 0 := by
  split_ifs <;> simp [expect, *]

@[simp] lemma expect_dite_eq' (i : ι) (f : ∀ j, j = i → α) :
    𝔼 j ∈ s, (if h : j = i then f j h else 0) = if i ∈ s then f i rfl / s.card else 0 := by
  split_ifs <;> simp [expect, *]

@[simp] lemma expect_ite_eq (i : ι) (f : ι → α) :
    𝔼 j ∈ s, (if i = j then f j else 0) = if i ∈ s then f i / s.card else 0 := by
  split_ifs <;> simp [expect, *]

@[simp] lemma expect_ite_eq' (i : ι) (f : ι → α) :
    𝔼 j ∈ s, (if j = i then f j else 0) = if i ∈ s then f i / s.card else 0 := by
  split_ifs <;> simp [expect, *]

end DecidableEq

section bij
variable {t : Finset κ} {g : κ → α}

-- TODO: Backport arguments changes to `card_congr` and `prod_bij`
lemma expect_bij (i : ∀ a ∈ s, κ) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b) : 𝔼 x ∈ s, f x = 𝔼 x ∈ t, g x := by
  rw [expect, expect, card_congr i hi (fun _ _ _ _ ↦ i_inj _ _ _ _),
    sum_bij i hi h (fun _ _ _ _ ↦ i_inj _ _ _ _) (by simpa [eq_comm] using i_surj)]
  simpa [eq_comm] using i_surj

lemma expect_nbij (i : ι → κ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
    (i_inj : (s : Set ι).InjOn i) (i_surj : (s : Set ι).SurjOn i t) :
    𝔼 x ∈ s, f x = 𝔼 x ∈ t, g x :=
  expect_bij (fun a _ ↦ i a) hi h i_inj $ by simpa [Set.SurjOn, Set.subset_def] using i_surj

lemma expect_bij' (i : ∀ a ∈ s, κ) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
    (j : ∀ a ∈ t, ι) (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) : 𝔼 x ∈ s, f x = 𝔼 x ∈ t, g x := by
  rw [expect, expect, sum_bij' i hi h j hj left_inv right_inv, card_congr i hi]
  · intro a b ha hb z
    rw [←left_inv a ha, ←left_inv b hb]
    congr 1
  intro b hb
  exact ⟨j b hb, hj _ _, right_inv _ _⟩

lemma expect_nbij' (i : ι → κ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a)) (j : κ → ι)
    (hj : ∀ a ∈ t, j a ∈ s) (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a) :
    𝔼 x ∈ s, f x = 𝔼 x ∈ t, g x :=
  expect_bij' (fun a _ ↦ i a) hi h (fun b _ ↦ j b) hj left_inv right_inv

/-- `Finset.expect_equiv` is a specialization of `Finset.expect_bij` that automatically fills in
most arguments. -/
lemma expect_equiv (e : ι ≃ κ) (hst : ∀ i, i ∈ s ↔ e i ∈ t) (hfg : ∀ i ∈ s, f i = g (e i)) :
    𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i :=
  expect_nbij e (fun i ↦ (hst _).1) hfg (e.injective.injOn _) fun i hi ↦ ⟨e.symm i, by simpa [hst]⟩

lemma expect_product' (f : ι → κ → α) : 𝔼 x ∈ s ×ˢ t, f x.1 x.2 = 𝔼 x ∈ s, 𝔼 y ∈ t, f x y := by
  simp only [expect, expect, card_product, sum_product', ←sum_div, div_div, mul_comm s.card,
    Nat.cast_mul]

end bij

lemma _root_.map_expect {F : Type*} [RingHomClass F α 𝕝] (g : F) (f : ι → α) (s : Finset ι) :
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

@[simp] nonrec lemma _root_.Fintype.sum_div_card [Fintype ι] (f : ι → α) :
    (∑ i, f i) / Fintype.card ι = 𝔼 i, f i := rfl

@[simp] nonrec lemma _root_.Fintype.card_smul_expect [Fintype ι] (f : ι → α) :
    Fintype.card ι • 𝔼 i, f i = ∑ i, f i := card_smul_expect _ _

@[simp] nonrec lemma _root_.Fintype.card_mul_expect [Fintype ι] (f : ι → α) :
    ↑(Fintype.card ι) * 𝔼 i, f i = ∑ i, f i :=
  card_mul_expect _ _

@[simp] lemma expect_const (hs : s.Nonempty) (a : α) : 𝔼 _i ∈ s, a = a := by
  rw [expect, sum_const, nsmul_eq_mul, mul_div_cancel_left]
  exact Nat.cast_ne_zero.2 hs.card_pos.ne'

lemma expect_indicate_eq [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι → α) (x : ι) :
    𝔼 i, ite (x = i) (Fintype.card ι : α) 0 * f i = f x := by
  simp_rw [expect_univ, ite_mul, zero_mul, sum_ite_eq, if_pos (mem_univ _)]
  rw [mul_div_cancel_left]
  simp [Fintype.card_ne_zero]

lemma expect_indicate_eq' [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι → α) (x : ι) :
    𝔼 i, ite (i = x) (Fintype.card ι : α) 0 * f i = f x := by
  simp_rw [@eq_comm _ _ x, expect_indicate_eq]

lemma smul_expect {G : Type*} [DistribSMul G α] [IsScalarTower G α α] (a : G)
    (s : Finset ι) (f : ι → α) : a • 𝔼 i ∈ s, f i = 𝔼 i ∈ s, a • f i := by
  simp only [expect, ← smul_div_assoc, smul_sum]

end Semifield

section Field
variable [Field α] [Field 𝕝] {s : Finset ι}

lemma expect_sub_distrib (s : Finset ι) (f g : ι → α) :
    𝔼 i ∈ s, (f i - g i) = 𝔼 i ∈ s, f i - 𝔼 i ∈ s, g i := by
  rw [expect, expect, expect, sum_sub_distrib, sub_div]

@[simp]
lemma expect_neg_distrib (s : Finset ι) (f : ι → α) : 𝔼 i ∈ s, -f i = -𝔼 i ∈ s, f i := by
  simp [expect, neg_div]

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

/-- This is a variant (beta-reduced) version of the standard lemma `Finset.prod_le_prod'`,
convenient for the `gcongr` tactic. -/
@[gcongr]
lemma _root_.GCongr.expect_le_expect (h : ∀ i ∈ s, f i ≤ g i) : s.expect f ≤ s.expect g :=
  Finset.expect_le_expect h

lemma expect_le (hs : s.Nonempty) (f : ι → α) (a : α) (h : ∀ x ∈ s, f x ≤ a) : 𝔼 i ∈ s, f i ≤ a :=
  (div_le_iff' $ Nat.cast_pos.2 hs.card_pos).2 $ by
    rw [←nsmul_eq_mul]; exact sum_le_card_nsmul _ _ _ h

lemma le_expect (hs : s.Nonempty) (f : ι → α) (a : α) (h : ∀ x ∈ s, a ≤ f x) : a ≤ 𝔼 i ∈ s, f i :=
  (le_div_iff' $ Nat.cast_pos.2 hs.card_pos).2 $ by
    rw [←nsmul_eq_mul]; exact card_nsmul_le_sum _ _ _ h

lemma expect_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ 𝔼 i ∈ s, f i :=
  div_nonneg (sum_nonneg hf) $ by positivity

lemma expect_pos (hf : ∀ i ∈ s, 0 < f i) (hs : s.Nonempty) : 0 < 𝔼 i ∈ s, f i :=
  div_pos (sum_pos hf hs) $ by positivity

lemma expect_eq_zero_iff_of_nonneg (hs : s.Nonempty) (hf : ∀ i ∈ s, 0 ≤ f i) :
    𝔼 i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  simp [expect, sum_eq_zero_iff_of_nonneg hf, hs.ne_empty]

lemma expect_eq_zero_iff_of_nonpos (hs : s.Nonempty) (hf : ∀ i ∈ s, f i ≤ 0) :
    𝔼 i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  simp [expect, sum_eq_zero_iff_of_nonpos hf, hs.ne_empty]

-- TODO: Contribute back better docstring to `le_prod_of_submultiplicative`
/-- If `m` is a subadditive function (`m (x * y) ≤ f x * f y`, `f 1 = 1`), and `f i`,
`i ∈ s`, is a finite family of elements, then `f (𝔼 i in s, g i) ≤ 𝔼 i in s, f (g i)`. -/
lemma le_expect_of_subadditive [LinearOrderedSemifield κ] (m : α → κ) (h_zero : m 0 = 0)
    (h_add : ∀ a b, m (a + b) ≤ m a + m b) (h_div : ∀ a (n : ℕ), m (a / n) = m a / n)
    (s : Finset ι) (f : ι → α) : m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i) := by
  simp only [expect, h_div]
  exact div_le_div_of_nonneg_right (le_sum_of_subadditive _ h_zero h_add _ _) $ by positivity

end LinearOrderedSemifield

section LinearOrderedField
variable [LinearOrderedField α] {s : Finset ι} {f g : ι → α}

lemma abs_expect_le_expect_abs (s : Finset ι) (f : ι → α) :
    |𝔼 i ∈ s, f i| ≤ 𝔼 i ∈ s, |f i| :=
  le_expect_of_subadditive _ abs_zero abs_add (by simp [abs_div]) _ _

end LinearOrderedField
end Finset

namespace algebraMap
variable {R A : Type*} [Semifield R] [Semifield A] [Algebra R A]

@[simp, norm_cast]
lemma coe_expect (s : Finset ι) (a : ι → R) : 𝔼 i ∈ s, a i = 𝔼 i ∈ s, (a i : A) :=
  map_expect (algebraMap R A) a s

end algebraMap

open Finset

namespace Fintype
variable {κ : Type*} [Fintype ι] [Fintype κ]

section Semifield
variable [Semifield α]

/-- `Fintype.expect_bijective` is a variant of `Finset.expect_bij` that accepts
`Function.Bijective`.

See `Function.Bijective.expect_comp` for a version without `h`. -/
lemma expect_bijective (e : ι → κ) (he : Bijective e) (f : ι → α) (g : κ → α)
    (h : ∀ x, f x = g (e x)) : 𝔼 i, f i = 𝔼 i, g i :=
  expect_nbij (fun _ ↦ e _) (fun _ _ ↦ mem_univ _) (fun x _ ↦ h x) (he.injective.injOn _) $ by
    simpa using he.surjective.surjOn _

/-- `Fintype.expect_equiv` is a specialization of `Finset.expect_bij` that automatically fills in
most arguments.

See `Equiv.expect_comp` for a version without `h`. -/
lemma expect_equiv (e : ι ≃ κ) (f : ι → α) (g : κ → α) (h : ∀ x, f x = g (e x)) :
    𝔼 i, f i = 𝔼 i, g i :=
  expect_bijective _ e.bijective f g h

@[simp] lemma expect_const [Nonempty ι] [CharZero α] (a : α) : 𝔼 _i : ι, a = a :=
  Finset.expect_const univ_nonempty _

@[simp] lemma expect_one [Nonempty ι] [CharZero α] : 𝔼 _i : ι, (1 : α) = 1 := expect_const _

lemma expect_ite_zero (p : ι → Prop) [DecidablePred p] (h : ∀ i j, p i → p j → i = j) (a : α) :
    𝔼 i, ite (p i) a 0 = ite (∃ i, p i) (a / Fintype.card ι) 0 := by
  simp [univ.expect_ite_zero p (by simpa using h), card_univ]

variable [DecidableEq ι]

@[simp] lemma expect_dite_eq (i : ι) (f : ∀ j, i = j → α) :
    𝔼 j, (if h : i = j then f j h else 0) = f i rfl / card ι := by simp [card_univ]

@[simp] lemma expect_dite_eq' (i : ι) (f : ∀ j, j = i → α) :
    𝔼 j, (if h : j = i then f j h else 0) = f i rfl / card ι := by simp [card_univ]

@[simp]
lemma expect_ite_eq (i : ι) (f : ι → α) : 𝔼 j, (if i = j then f j else 0) = f i / card ι := by
  simp [card_univ]

@[simp]
lemma expect_ite_eq' (i : ι) (f : ι → α) : 𝔼 j, (if j = i then f j else 0) = f i / card ι := by
  simp [card_univ]

end Semifield

section LinearOrderedSemifield
variable [LinearOrderedSemifield α] [Nonempty ι] {f : ι → α}

lemma expect_eq_zero_iff_of_nonneg (hf : 0 ≤ f) : 𝔼 i, f i = 0 ↔ f = 0 := by
  simp [expect, sum_eq_zero_iff_of_nonneg hf, univ_nonempty.ne_empty]

lemma expect_eq_zero_iff_of_nonpos (hf : f ≤ 0) : 𝔼 i, f i = 0 ↔ f = 0 := by
  simp [expect, sum_eq_zero_iff_of_nonpos hf, univ_nonempty.ne_empty]

end LinearOrderedSemifield
end Fintype

namespace IsROrC
variable [IsROrC α] [Fintype ι] (f : ι → ℝ) (a : ι)

@[simp, norm_cast]
lemma coe_balance : (↑(balance f a) : α) = balance ((↑) ∘ f) a := map_balance (algebraMap ℝ α) _ _

@[simp] lemma coe_comp_balance : ((↑) : ℝ → α) ∘ balance f = balance ((↑) ∘ f) :=
  funext $ coe_balance _

end IsROrC

open Finset

namespace Mathlib.Meta.Positivity
open Qq Lean Meta

@[positivity Finset.expect _ _]
def evalFinsetExpect : PositivityExt where eval {u α} zα pα e := do
  match e with
  | ~q(@Finset.expect $ι _ $instα $s $f) =>
    let (lhs, _, (rhs : Q($α))) ← lambdaMetaTelescope f
    let so : Option Q(Finset.Nonempty $s) ← do -- TODO: It doesn't complain if we make a typo?
      try
        let _fi ← synthInstanceQ q(Fintype $ι)
        let _no ← synthInstanceQ q(Nonempty $ι)
        match s with
        | ~q(@univ _ $fi) => pure (some q(Finset.univ_nonempty (α := $ι)))
        | _ => pure none
      catch _ => do
        let .some fv ← findLocalDeclWithType? q(Finset.Nonempty $s) | pure none
        pure (some (.fvar fv))
    match ← core zα pα rhs, so with
    | .nonnegative pb, _ => do
      let instα' ← synthInstanceQ q(LinearOrderedSemifield $α)
      assertInstancesCommute
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars lhs pb
      pure (.nonnegative q(@expect_nonneg $ι $α $instα' $s $f fun i _ ↦ $pr i))
    | .positive pb, .some (fi : Q(Finset.Nonempty $s)) => do
      let instα' ← synthInstanceQ q(LinearOrderedSemifield $α)
      assertInstancesCommute
      let pr : Q(∀ i, 0 < $f i) ← mkLambdaFVars lhs pb
      pure (.positive q(@expect_pos $ι $α $instα' $s $f (fun i _ ↦ $pr i) $fi))
    | _, _ => pure .none
  | _ => throwError "not Finset.expect"

example (n : ℕ) (a : ℕ → ℝ) : 0 ≤ 𝔼 j ∈ range n, a j^2 := by positivity
example (a : ULift.{2} ℕ → ℝ) (s : Finset (ULift.{2} ℕ)) : 0 ≤ 𝔼 j ∈ s, a j^2 := by positivity
example (n : ℕ) (a : ℕ → ℝ) : 0 ≤ 𝔼 j : Fin 8, 𝔼 i ∈ range n, (a j^2 + i ^ 2) := by positivity
example (n : ℕ) (a : ℕ → ℝ) : 0 < 𝔼 j : Fin (n + 1), (a j^2 + 1) := by positivity
example (a : ℕ → ℝ) : 0 < 𝔼 j ∈ ({1} : Finset ℕ), (a j^2 + 1) := by
  have : Finset.Nonempty {1} := singleton_nonempty 1
  positivity

end Mathlib.Meta.Positivity
