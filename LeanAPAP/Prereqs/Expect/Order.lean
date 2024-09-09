import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Module.Rat
import Mathlib.Data.Finset.Pointwise.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.NNRat.Order
import LeanAPAP.Prereqs.Expect.Basic

/-!
# Order properties of the average over a finset
-/

open Function
open Fintype (card)
open scoped BigOperators Pointwise NNRat

variable {ι κ α β R : Type*}

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

namespace Finset
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
variable [PosSMulMono ℚ≥0 α]

lemma expect_le_expect (hfg : ∀ i ∈ s, f i ≤ g i) : 𝔼 i ∈ s, f i ≤ 𝔼 i ∈ s, g i :=
  smul_le_smul_of_nonneg_left (sum_le_sum hfg) $ by positivity

/-- This is a (beta-reduced) version of the standard lemma `Finset.expect_le_expect`,
convenient for the `gcongr` tactic. -/
@[gcongr]
lemma _root_.GCongr.expect_le_expect (h : ∀ i ∈ s, f i ≤ g i) : s.expect f ≤ s.expect g :=
  Finset.expect_le_expect h

lemma expect_le (hs : s.Nonempty) (f : ι → α) (a : α) (h : ∀ x ∈ s, f x ≤ a) : 𝔼 i ∈ s, f i ≤ a :=
  (inv_smul_le_iff_of_pos $ mod_cast hs.card_pos).2 $ by
    rw [Nat.cast_smul_eq_nsmul]; exact sum_le_card_nsmul _ _ _ h

lemma le_expect (hs : s.Nonempty) (f : ι → α) (a : α) (h : ∀ x ∈ s, a ≤ f x) : a ≤ 𝔼 i ∈ s, f i :=
  (le_inv_smul_iff_of_pos $ mod_cast hs.card_pos).2 $ by
    rw [Nat.cast_smul_eq_nsmul]; exact card_nsmul_le_sum _ _ _ h

lemma expect_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ 𝔼 i ∈ s, f i :=
  smul_nonneg (by positivity) $ sum_nonneg hf

end PosSMulMono

section PosSMulMono
variable {M N : Type*} [AddCommMonoid M] [Module ℚ≥0 M] [OrderedAddCommMonoid N] [Module ℚ≥0 N]
  [PosSMulMono ℚ≥0 N]

-- TODO: Contribute back better docstring to `le_prod_of_submultiplicative`
/-- If `m` is a subadditive function (`m (x + y) ≤ m x + m y`, `f 1 = 1`), and `f i`,
`i ∈ s`, is a finite family of elements, then `m (𝔼 i in s, f i) ≤ 𝔼 i in s, m (f i)`. -/
lemma le_expect_of_subadditive (m : M → N) (h_zero : m 0 = 0)
    (h_add : ∀ a b, m (a + b) ≤ m a + m b) (h_div : ∀ a (n : ℕ), m (a /ℚ n) = m a /ℚ n)
    (s : Finset ι) (f : ι → M) : m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i) := by
  simp only [expect, h_div]
  exact smul_le_smul_of_nonneg_left (le_sum_of_subadditive _ h_zero h_add _ _) $ by positivity

end PosSMulMono
end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid
variable [OrderedCancelAddCommMonoid α] [Module ℚ≥0 α] {s : Finset ι} {f g : ι → α}
section PosSMulStrictMono
variable [PosSMulStrictMono ℚ≥0 α]

lemma expect_pos (hf : ∀ i ∈ s, 0 < f i) (hs : s.Nonempty) : 0 < 𝔼 i ∈ s, f i :=
  smul_pos (inv_pos.2 $ mod_cast hs.card_pos) $ sum_pos hf hs

end PosSMulStrictMono
end OrderedCancelAddCommMonoid

section LinearOrderedAddCommGroup
variable [LinearOrderedAddCommGroup α] [Module ℚ≥0 α] [PosSMulMono ℚ≥0 α]

lemma abs_expect_le_expect_abs (s : Finset ι) (f : ι → α) : |𝔼 i ∈ s, f i| ≤ 𝔼 i ∈ s, |f i| :=
  le_expect_of_subadditive _ abs_zero abs_add (fun _ _ ↦ abs_nnqsmul _ _) _ _

end LinearOrderedAddCommGroup

section LinearOrderedCommSemiring
variable [LinearOrderedCommSemiring R] [ExistsAddOfLE R] [Module ℚ≥0 R] [PosSMulMono ℚ≥0 R]

/-- **Cauchy-Schwarz inequality** for finsets. -/
lemma expect_mul_sq_le_sq_mul_sq (s : Finset ι) (f g : ι → R) :
    (𝔼 i ∈ s, f i * g i) ^ 2 ≤ (𝔼 i ∈ s, f i ^ 2) * 𝔼 i ∈ s, g i ^ 2 := by
  simp only [expect, smul_pow, inv_pow, smul_mul_smul_comm, ← sq]
  gcongr
  exact sum_mul_sq_le_sq_mul_sq ..

end LinearOrderedCommSemiring
end Finset

open Finset

namespace Fintype
variable [Fintype ι] [Fintype κ]

section OrderedAddCommMonoid
variable [OrderedAddCommMonoid α] [Module ℚ≥0 α] {f : ι → α}

lemma expect_eq_zero_iff_of_nonneg [Nonempty ι] (hf : 0 ≤ f) : 𝔼 i, f i = 0 ↔ f = 0 := by
  simp [expect, sum_eq_zero_iff_of_nonneg hf, univ_nonempty.ne_empty]

lemma expect_eq_zero_iff_of_nonpos [Nonempty ι] (hf : f ≤ 0) : 𝔼 i, f i = 0 ↔ f = 0 := by
  simp [expect, sum_eq_zero_iff_of_nonpos hf, univ_nonempty.ne_empty]

end OrderedAddCommMonoid
end Fintype

open Finset

namespace Mathlib.Meta.Positivity
open Qq Lean Meta Finset
open scoped BigOperators

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
