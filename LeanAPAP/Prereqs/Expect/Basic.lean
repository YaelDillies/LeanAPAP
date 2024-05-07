import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Positivity.Finset
import LeanAPAP.Mathlib.Algebra.Algebra.Basic
import LeanAPAP.Mathlib.Algebra.Order.Module.Defs
import LeanAPAP.Mathlib.Data.Fintype.Pi

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

open Function
open Fintype (card)
open scoped Pointwise NNRat NNReal

variable {ι κ α β : Type*}

-- TODO: Localise
notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

/-- Average of a function over a finset. If the finset is empty, this is equal to zero. -/
def Finset.expect [AddCommMonoid α] [Module ℚ≥0 α] (s : Finset ι) (f : ι → α) : α :=
  (s.card : ℚ≥0)⁻¹ • s.sum f

namespace BigOperators
open Batteries.ExtendedBinder Lean Meta

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
open Batteries.ExtendedBinder

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

end BigOperators

open scoped BigOperators

namespace Finset
section AddCommMonoid
variable [AddCommMonoid α] [Module ℚ≥0 α] [AddCommMonoid β] [Module ℚ≥0 β] {s : Finset ι}
  {f g : ι → α} {m : β → α}

lemma expect_univ [Fintype ι] : 𝔼 x, f x = (∑ x, f x) /ℚ Fintype.card ι := by
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

lemma expect_sum_comm (s : Finset ι) (t : Finset κ) (f : ι → κ → α) :
    𝔼 i ∈ s, ∑ j ∈ t, f i j = ∑ j ∈ t, 𝔼 i ∈ s, f i j := by
  simpa only [expect, smul_sum] using sum_comm

lemma expect_comm (s : Finset ι) (t : Finset κ) (f : ι → κ → α) :
    𝔼 i ∈ s, 𝔼 j ∈ t, f i j = 𝔼 j ∈ t, 𝔼 i ∈ s, f i j := by
  rw [expect, expect, ←expect_sum_comm, ←expect_sum_comm, expect, expect, smul_comm, sum_comm]

lemma expect_eq_zero (h : ∀ i ∈ s, f i = 0) : 𝔼 i ∈ s, f i = 0 :=
  (expect_congr rfl h).trans s.expect_const_zero

-- TODO: Golf `exists_ne_zero_of_sum_ne_zero`
lemma exists_ne_zero_of_expect_ne_zero (h : 𝔼 i ∈ s, f i ≠ 0) : ∃ i ∈ s, f i ≠ 0 := by
  contrapose! h; exact expect_eq_zero h

lemma expect_add_distrib (s : Finset ι) (f g : ι → α) :
    𝔼 i ∈ s, (f i + g i) = 𝔼 i ∈ s, f i + 𝔼 i ∈ s, g i := by
  simp [expect, sum_add_distrib]

lemma expect_add_expect_comm (f₁ f₂ g₁ g₂ : ι → α) :
    𝔼 i ∈ s, (f₁ i + f₂ i) + 𝔼 i ∈ s, (g₁ i + g₂ i) =
      𝔼 i ∈ s, (f₁ i + g₁ i) + 𝔼 i ∈ s, (f₂ i + g₂ i) := by
  simp_rw [expect_add_distrib, add_add_add_comm]

lemma expect_eq_single_of_mem (i : ι) (hi : i ∈ s) (h : ∀ j ∈ s, j ≠ i → f j = 0) :
    𝔼 i ∈ s, f i = f i /ℚ s.card := by rw [expect, sum_eq_single_of_mem _ hi h]

/-- See also `Finset.expect_boole`. -/
lemma expect_ite_zero (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    (h : ∀ i ∈ s, ∀ j ∈ s, p i → p j → i = j) (a : α) :
    𝔼 i ∈ s, ite (p i) a 0 = ite (∃ i ∈ s, p i) (a /ℚ s.card) 0 := by
  split_ifs <;> simp [expect, sum_ite_zero _ _ h, *]

section DecidableEq
variable [DecidableEq ι]

@[simp] lemma expect_dite_eq (i : ι) (f : ∀ j, i = j → α) :
    𝔼 j ∈ s, (if h : i = j then f j h else 0) = if i ∈ s then f i rfl /ℚ s.card else 0 := by
  split_ifs <;> simp [expect, *]

@[simp] lemma expect_dite_eq' (i : ι) (f : ∀ j, j = i → α) :
    𝔼 j ∈ s, (if h : j = i then f j h else 0) = if i ∈ s then f i rfl /ℚ s.card else 0 := by
  split_ifs <;> simp [expect, *]

@[simp] lemma expect_ite_eq (i : ι) (f : ι → α) :
    𝔼 j ∈ s, (if i = j then f j else 0) = if i ∈ s then f i /ℚ s.card else 0 := by
  split_ifs <;> simp [expect, *]

@[simp] lemma expect_ite_eq' (i : ι) (f : ι → α) :
    𝔼 j ∈ s, (if j = i then f j else 0) = if i ∈ s then f i /ℚ s.card else 0 := by
  split_ifs <;> simp [expect, *]

end DecidableEq

section bij
variable {t : Finset κ} {g : κ → α}

-- TODO: Backport arguments changes to `card_congr` and `prod_bij`
lemma expect_bij (i : ∀ a ∈ s, κ) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b) : 𝔼 x ∈ s, f x = 𝔼 x ∈ t, g x := by
  rw [expect, expect, card_congr i hi (fun _ _ _ ↦ i_inj _ _ _) (by simpa using i_surj),
    sum_bij i hi (fun _ _ _ ↦ i_inj _ _ _) (by simpa using i_surj) h]

lemma expect_nbij (i : ι → κ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
    (i_inj : (s : Set ι).InjOn i) (i_surj : (s : Set ι).SurjOn i t) :
    𝔼 x ∈ s, f x = 𝔼 x ∈ t, g x :=
  expect_bij (fun a _ ↦ i a) hi h i_inj $ by simpa [Set.SurjOn, Set.subset_def] using i_surj

lemma expect_bij' (i : ∀ a ∈ s, κ) (j : ∀ a ∈ t, ι) (hi : ∀ a ha, i a ha ∈ t)
    (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) (h : ∀ a ha, f a = g (i a ha)) :
    𝔼 x ∈ s, f x = 𝔼 x ∈ t, g x := by
  rw [expect, expect, sum_bij' i j hi hj left_inv right_inv h, card_congr i hi]
  · intro a b ha hb z
    rw [←left_inv a ha, ←left_inv b hb]
    congr 1
  · exact fun b hb ↦ ⟨j b hb, hj _ _, right_inv _ _⟩

lemma expect_nbij' (i : ι → κ) (j : κ → ι) (hi : ∀ a ∈ s, i a ∈ t) (hj : ∀ a ∈ t, j a ∈ s)
    (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a)
    (h : ∀ a ∈ s, f a = g (i a)) : 𝔼 x ∈ s, f x = 𝔼 x ∈ t, g x :=
  expect_bij' (fun a _ ↦ i a) (fun b _ ↦ j b) hi hj left_inv right_inv h

/-- `Finset.expect_equiv` is a specialization of `Finset.expect_bij` that automatically fills in
most arguments. -/
lemma expect_equiv (e : ι ≃ κ) (hst : ∀ i, i ∈ s ↔ e i ∈ t) (hfg : ∀ i ∈ s, f i = g (e i)) :
    𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i :=
  expect_nbij e (fun i ↦ (hst _).1) hfg (e.injective.injOn _) fun i hi ↦ ⟨e.symm i, by simpa [hst]⟩

lemma expect_product' (f : ι → κ → α) : 𝔼 x ∈ s ×ˢ t, f x.1 x.2 = 𝔼 x ∈ s, 𝔼 y ∈ t, f x y := by
  simp only [expect, card_product, sum_product', smul_sum, mul_inv, mul_smul, Nat.cast_mul]

-- TODO: Change assumption of `prod_image` to `Set.InjOn`
@[simp]
lemma expect_image [DecidableEq ι] {m : κ → ι} (hm : (t : Set κ).InjOn m) :
    𝔼 i ∈ t.image m, f i = 𝔼 i ∈ t, f (m i) := by
  simp_rw [expect, card_image_of_injOn hm, sum_image hm]

end bij

@[simp] lemma expect_inv_index [DecidableEq ι] [InvolutiveInv ι] (s : Finset ι) (f : ι → α) :
    𝔼 i ∈ s⁻¹, f i = 𝔼 i ∈ s, f i⁻¹ := expect_image $ inv_injective.injOn _

@[simp] lemma expect_neg_index [DecidableEq ι] [InvolutiveNeg ι] (s : Finset ι) (f : ι → α) :
    𝔼 i ∈ -s, f i = 𝔼 i ∈ s, f (-i) := expect_image $ neg_injective.injOn _

lemma _root_.map_expect {F : Type*} [FunLike F α β] [LinearMapClass F ℚ≥0 α β]
    (g : F) (f : ι → α) (s : Finset ι) :
    g (𝔼 x ∈ s, f x) = 𝔼 x ∈ s, g (f x) := by simp only [expect, map_smul, map_natCast, map_sum]

@[simp]
lemma card_smul_expect (s : Finset ι) (f : ι → α) : s.card • 𝔼 i ∈ s, f i = ∑ i ∈ s, f i := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [expect, nsmul_eq_smul_cast ℚ≥0, smul_inv_smul₀]
    positivity

@[simp] nonrec lemma _root_.Fintype.card_smul_expect [Fintype ι] (f : ι → α) :
    Fintype.card ι • 𝔼 i, f i = ∑ i, f i := card_smul_expect _ _

@[simp] lemma expect_const (hs : s.Nonempty) (a : α) : 𝔼 _i ∈ s, a = a := by
  rw [expect, sum_const, nsmul_eq_smul_cast ℚ≥0, inv_smul_smul₀]; positivity

lemma smul_expect {G : Type*} [DistribSMul G α] [SMulCommClass G ℚ≥0 α] (a : G)
    (s : Finset ι) (f : ι → α) : a • 𝔼 i ∈ s, f i = 𝔼 i ∈ s, a • f i := by
  simp only [expect, smul_sum, smul_comm]

end AddCommMonoid

section AddCommGroup
variable [AddCommGroup α] [Module ℚ≥0 α] [Field β] [Module ℚ≥0 β] {s : Finset ι}

lemma expect_sub_distrib (s : Finset ι) (f g : ι → α) :
    𝔼 i ∈ s, (f i - g i) = 𝔼 i ∈ s, f i - 𝔼 i ∈ s, g i := by
  simp only [expect, sum_sub_distrib, smul_sub]

@[simp]
lemma expect_neg_distrib (s : Finset ι) (f : ι → α) : 𝔼 i ∈ s, -f i = -𝔼 i ∈ s, f i := by
  simp [expect]

variable [Fintype ι]

def balance (f : ι → α) : ι → α := f - Function.const _ (𝔼 y, f y)

lemma balance_apply (f : ι → α) (x : ι) : balance f x = f x - 𝔼 y, f y := rfl

@[simp] lemma balance_zero : balance (0 : ι → α) = 0 := by simp [balance]

@[simp] lemma balance_add (f g : ι → α) : balance (f + g) = balance f + balance g := by
  simp only [balance, expect_add_distrib, ← const_add, add_sub_add_comm, Pi.add_apply]

@[simp] lemma balance_sub (f g : ι → α) : balance (f - g) = balance f - balance g := by
  simp only [balance, expect_sub_distrib, const_sub, sub_sub_sub_comm, Pi.sub_apply]

@[simp] lemma balance_neg (f : ι → α) : balance (-f) = -balance f := by
  simp only [balance, expect_neg_distrib, const_neg, neg_sub', Pi.neg_apply]

@[simp] lemma sum_balance (f : ι → α) : ∑ x, balance f x = 0 := by
  cases isEmpty_or_nonempty ι <;> simp [balance_apply]

@[simp] lemma expect_balance (f : ι → α) : 𝔼 x, balance f x = 0 := by simp [expect]

@[simp] lemma balance_idem (f : ι → α) : balance (balance f) = balance f := by
  cases isEmpty_or_nonempty ι <;> ext x <;> simp [balance, expect_sub_distrib, univ_nonempty]

@[simp] lemma map_balance {F : Type*} [FunLike F α β] [LinearMapClass F ℚ≥0 α β] (g : F) (f : ι → α)
    (a : ι) : g (balance f a) = balance (g ∘ f) a := by simp [balance, map_expect]

end AddCommGroup

section Semiring
variable [Semiring α] [Module ℚ≥0 α] {s : Finset ι} {f g : ι → α} {m : β → α}

@[simp] lemma card_mul_expect (s : Finset ι) (f : ι → α) :
    s.card * 𝔼 i ∈ s, f i = ∑ i ∈ s, f i := by rw [←nsmul_eq_mul, card_smul_expect]

@[simp] nonrec lemma _root_.Fintype.card_mul_expect [Fintype ι] (f : ι → α) :
    Fintype.card ι * 𝔼 i, f i = ∑ i, f i := card_mul_expect _ _

lemma expect_mul [IsScalarTower ℚ≥0 α α] (s : Finset ι) (f : ι → α) (a : α) :
    (𝔼 i ∈ s, f i) * a = 𝔼 i ∈ s, f i * a := by rw [expect, expect, smul_mul_assoc, sum_mul]

lemma mul_expect [SMulCommClass ℚ≥0 α α] (s : Finset ι) (f : ι → α) (a : α) :
    a * 𝔼 i ∈ s, f i = 𝔼 i ∈ s, a * f i := by rw [expect, expect, mul_smul_comm, mul_sum]

-- TODO: Change `sum_mul_sum` to match?
lemma expect_mul_expect [IsScalarTower ℚ≥0 α α] [SMulCommClass ℚ≥0 α α] (s : Finset ι)
    (t : Finset κ) (f : ι → α) (g : κ → α) :
    (𝔼 i ∈ s, f i) * 𝔼 j ∈ t, g j = 𝔼 i ∈ s, 𝔼 j ∈ t, f i * g j := by
  simp_rw [expect_mul, mul_expect]

end Semiring

section CommSemiring
variable [CommSemiring α] [Module ℚ≥0 α] [IsScalarTower ℚ≥0 α α] [SMulCommClass ℚ≥0 α α]

lemma expect_pow (s : Finset ι) (f : ι → α) (n : ℕ) :
    (𝔼 i ∈ s, f i) ^ n = 𝔼 p ∈ s ^^ n, ∏ i, f (p i) := by
  classical
  rw [expect, smul_pow, sum_pow', expect, Fintype.card_piFinsetConst, inv_pow, Nat.cast_pow]

end CommSemiring

section Semifield
variable [Semifield α] [CharZero α] [SMul ℚ≥0 α] {s : Finset ι} {f g : ι → α}
  {m : β → α}

lemma expect_indicate_eq [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι → α) (x : ι) :
    𝔼 i, ite (x = i) (Fintype.card ι : α) 0 * f i = f x := by
  simp_rw [expect_univ, ite_mul, zero_mul, sum_ite_eq, if_pos (mem_univ _)]
  rw [←@NNRat.cast_natCast α, ←NNRat.smul_def, inv_smul_smul₀]
  simp [Fintype.card_ne_zero]

lemma expect_indicate_eq' [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι → α) (x : ι) :
    𝔼 i, ite (i = x) (Fintype.card ι : α) 0 * f i = f x := by
  simp_rw [@eq_comm _ _ x, expect_indicate_eq]

lemma expect_eq_sum_div_card (s : Finset ι) (f : ι → α) :
    𝔼 i ∈ s, f i = (∑ i ∈ s, f i) / s.card := by
  rw [expect, NNRat.smul_def, div_eq_inv_mul, NNRat.cast_inv, NNRat.cast_natCast]

nonrec lemma _root_.Fintype.expect_eq_sum_div_card [Fintype ι] (f : ι → α) :
    𝔼 i, f i = (∑ i, f i) / Fintype.card ι := Finset.expect_eq_sum_div_card _ _

lemma expect_div (s : Finset ι) (f : ι → α) (a : α) : (𝔼 i ∈ s, f i) / a = 𝔼 i ∈ s, f i / a := by
  simp_rw [div_eq_mul_inv, expect_mul]

end Semifield

/-! ### Order -/

section OrderedAddCommMonoid
variable [OrderedAddCommMonoid α] [Module ℚ≥0 α] [OrderedAddCommMonoid β] [Module ℚ≥0 β]
  {s : Finset ι} {f g : ι → α}

lemma expect_eq_zero_iff_of_nonneg (hs : s.Nonempty) (hf : ∀ i ∈ s, 0 ≤ f i) :
    𝔼 i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  simp [expect, sum_eq_zero_iff_of_nonneg hf, hs.ne_empty]

lemma expect_eq_zero_iff_of_nonpos (hs : s.Nonempty) (hf : ∀ i ∈ s, f i ≤ 0) :
    𝔼 i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  simp [expect, sum_eq_zero_iff_of_nonpos hf, hs.ne_empty]

section PosSMulMono
variable [PosSMulMono ℚ≥0 α] [PosSMulMono ℚ≥0 β]

lemma expect_le_expect (hfg : ∀ i ∈ s, f i ≤ g i) : 𝔼 i ∈ s, f i ≤ 𝔼 i ∈ s, g i :=
  smul_le_smul_of_nonneg_left (sum_le_sum hfg) $ by positivity

/-- This is a (beta-reduced) version of the standard lemma `Finset.expect_le_expect`,
convenient for the `gcongr` tactic. -/
@[gcongr]
lemma _root_.GCongr.expect_le_expect (h : ∀ i ∈ s, f i ≤ g i) : s.expect f ≤ s.expect g :=
  Finset.expect_le_expect h

lemma expect_le (hs : s.Nonempty) (f : ι → α) (a : α) (h : ∀ x ∈ s, f x ≤ a) : 𝔼 i ∈ s, f i ≤ a :=
  (inv_smul_le_iff_of_pos $ by positivity).2 $ by
    rw [←nsmul_eq_smul_cast]; exact sum_le_card_nsmul _ _ _ h

lemma le_expect (hs : s.Nonempty) (f : ι → α) (a : α) (h : ∀ x ∈ s, a ≤ f x) : a ≤ 𝔼 i ∈ s, f i :=
  (le_inv_smul_iff_of_pos $ by positivity).2 $ by
    rw [←nsmul_eq_smul_cast]; exact card_nsmul_le_sum _ _ _ h

lemma expect_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ 𝔼 i ∈ s, f i :=
  smul_nonneg (by positivity) $ sum_nonneg hf

-- TODO: Contribute back better docstring to `le_prod_of_submultiplicative`
/-- If `m` is a subadditive function (`m (x + y) ≤ m x + m y`, `f 1 = 1`), and `f i`,
`i ∈ s`, is a finite family of elements, then `m (𝔼 i in s, f i) ≤ 𝔼 i in s, m (f i)`. -/
lemma le_expect_of_subadditive (m : α → β) (h_zero : m 0 = 0)
    (h_add : ∀ a b, m (a + b) ≤ m a + m b) (h_div : ∀ a (n : ℕ), m (a /ℚ n) = m a /ℚ n)
    (s : Finset ι) (f : ι → α) : m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i) := by
  simp only [expect, h_div]
  exact smul_le_smul_of_nonneg_left (le_sum_of_subadditive _ h_zero h_add _ _) $ by positivity

end PosSMulMono
end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid
variable [OrderedCancelAddCommMonoid α] [Module ℚ≥0 α] {s : Finset ι} {f g : ι → α}
section PosSMulStrictMono
variable [PosSMulStrictMono ℚ≥0 α]

lemma expect_pos (hf : ∀ i ∈ s, 0 < f i) (hs : s.Nonempty) : 0 < 𝔼 i ∈ s, f i :=
  smul_pos (by positivity) $ sum_pos hf hs

end PosSMulStrictMono
end OrderedCancelAddCommMonoid

section LinearOrderedAddCommGroup
variable [LinearOrderedAddCommGroup α] [Module ℚ≥0 α] [PosSMulMono ℚ≥0 α]

lemma abs_expect_le_expect_abs (s : Finset ι) (f : ι → α) : |𝔼 i ∈ s, f i| ≤ 𝔼 i ∈ s, |f i| :=
  le_expect_of_subadditive _ abs_zero abs_add (fun _ _ ↦ abs_nnqsmul _ _) _ _

end LinearOrderedAddCommGroup
end Finset

namespace algebraMap
variable [Semifield α] [CharZero α] [SMul ℚ≥0 α] [Semifield β] [CharZero β]
  [SMul ℚ≥0 β] [Algebra α β]

@[simp, norm_cast]
lemma coe_expect (s : Finset ι) (f : ι → α) : 𝔼 i ∈ s, f i = 𝔼 i ∈ s, (f i : β) :=
  map_expect (algebraMap _ _) _ _

end algebraMap

open Finset

namespace Fintype
variable [Fintype ι] [Fintype κ]

section AddCommMonoid
variable [AddCommMonoid α] [Module ℚ≥0 α] {f : ι → α}

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

@[simp] lemma expect_const [Nonempty ι] (a : α) : 𝔼 _i : ι, a = a :=
  Finset.expect_const univ_nonempty _

lemma expect_ite_zero (p : ι → Prop) [DecidablePred p] (h : ∀ i j, p i → p j → i = j) (a : α) :
    𝔼 i, ite (p i) a 0 = ite (∃ i, p i) (a /ℚ Fintype.card ι) 0 := by
  simp [univ.expect_ite_zero p (by simpa using h), card_univ]

variable [DecidableEq ι]

@[simp] lemma expect_dite_eq (i : ι) (f : ∀ j, i = j → α) :
    𝔼 j, (if h : i = j then f j h else 0) = f i rfl /ℚ card ι := by simp [card_univ]

@[simp] lemma expect_dite_eq' (i : ι) (f : ∀ j, j = i → α) :
    𝔼 j, (if h : j = i then f j h else 0) = f i rfl /ℚ card ι := by simp [card_univ]

@[simp] lemma expect_ite_eq (i : ι) (f : ι → α) :
    𝔼 j, (if i = j then f j else 0) = f i /ℚ card ι := by simp [card_univ]

@[simp] lemma expect_ite_eq' (i : ι) (f : ι → α) :
    𝔼 j, (if j = i then f j else 0) = f i /ℚ card ι := by simp [card_univ]

end AddCommMonoid

section Semiring
variable [Semiring α] [Module ℚ≥0 α]

@[simp] lemma expect_one [Nonempty ι] : 𝔼 _i : ι, (1 : α) = 1 := expect_const _

end Semiring

section OrderedAddCommMonoid
variable [OrderedAddCommMonoid α] [Module ℚ≥0 α] {f : ι → α}

lemma expect_eq_zero_iff_of_nonneg [Nonempty ι] (hf : 0 ≤ f) : 𝔼 i, f i = 0 ↔ f = 0 := by
  simp [expect, sum_eq_zero_iff_of_nonneg hf, univ_nonempty.ne_empty]

lemma expect_eq_zero_iff_of_nonpos [Nonempty ι] (hf : f ≤ 0) : 𝔼 i, f i = 0 ↔ f = 0 := by
  simp [expect, sum_eq_zero_iff_of_nonpos hf, univ_nonempty.ne_empty]

end OrderedAddCommMonoid
end Fintype

namespace RCLike
variable [RCLike α] [Fintype ι] (f : ι → ℝ) (a : ι)

@[simp, norm_cast]
lemma coe_balance : (↑(balance f a) : α) = balance ((↑) ∘ f) a := map_balance (algebraMap ℝ α) _ _

@[simp] lemma coe_comp_balance : ((↑) : ℝ → α) ∘ balance f = balance ((↑) ∘ f) :=
  funext $ coe_balance _

end RCLike

open Finset

instance [Preorder α] [MulAction ℚ α] [PosSMulMono ℚ α] : PosSMulMono ℚ≥0 α where
  elim a _ _b₁ _b₂ hb := (smul_le_smul_of_nonneg_left hb a.2 :)

instance LinearOrderedSemifield.toPosSMulStrictMono [LinearOrderedSemifield α] :
    PosSMulStrictMono ℚ≥0 α where
  elim a ha b₁ b₂ hb := by
    simp_rw [NNRat.smul_def]; exact mul_lt_mul_of_pos_left hb (NNRat.cast_pos.2 ha)

namespace Mathlib.Meta.Positivity
open Qq Lean Meta

@[positivity Finset.expect _ _]
def evalFinsetExpect : PositivityExt where eval {u α} zα pα e := do
  match e with
  | ~q(@Finset.expect $ι _ $instα $instmod $s $f) =>
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
      let instαordmon ← synthInstanceQ q(OrderedAddCommMonoid $α)
      let instαordsmul ← synthInstanceQ q(PosSMulMono ℚ≥0 $α)
      assumeInstancesCommute
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars lhs pb
      return .nonnegative q(@expect_nonneg $ι $α $instαordmon $instmod $s $f $instαordsmul
        fun i _ ↦ $pr i)
    | .positive pb, .some (fi : Q(Finset.Nonempty $s)) => do
      let instαordmon ← synthInstanceQ q(OrderedCancelAddCommMonoid $α)
      let instαordsmul ← synthInstanceQ q(PosSMulStrictMono ℚ≥0 $α)
      assumeInstancesCommute
      let pr : Q(∀ i, 0 < $f i) ← mkLambdaFVars lhs pb
      return .positive q(@expect_pos $ι $α $instαordmon $instmod $s $f $instαordsmul
        (fun i _ ↦ $pr i) $fi)
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
