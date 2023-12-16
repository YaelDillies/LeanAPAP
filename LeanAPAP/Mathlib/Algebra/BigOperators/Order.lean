import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Ring

open scoped BigOperators

namespace Mathlib.Meta.Positivity
open Qq Lean Meta Finset

@[positivity Finset.sum _ _]
def evalFinsetSum : PositivityExt where eval {u α} zα pα e := do
  match e with
  | ~q(@Finset.sum _ $ι $instα $s $f) =>
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
      let pα' ← synthInstanceQ q(OrderedAddCommMonoid $α)
      assertInstancesCommute
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars lhs pb
      pure (.nonnegative q(@sum_nonneg $ι $α $pα' $f $s fun i _ ↦ $pr i))
    | .positive pb, .some (fi : Q(Finset.Nonempty $s)) => do
      let pα' ← synthInstanceQ q(OrderedCancelAddCommMonoid $α)
      assertInstancesCommute
      let pr : Q(∀ i, 0 < $f i) ← mkLambdaFVars lhs pb
      pure (.positive q(@sum_pos $ι $α $pα' $f $s (fun i _ ↦ $pr i) $fi))
    | _, _ => pure .none
  | _ => throwError "not Finset.sum"

example (n : ℕ) (a : ℕ → ℤ) : 0 ≤ ∑ j in range n, a j^2 := by positivity
example (a : ULift.{2} ℕ → ℤ) (s : Finset (ULift.{2} ℕ)) : 0 ≤ ∑ j in s, a j^2 := by positivity
example (n : ℕ) (a : ℕ → ℤ) : 0 ≤ ∑ j : Fin 8, ∑ i in range n, (a j^2 + i ^ 2) := by positivity
example (n : ℕ) (a : ℕ → ℤ) : 0 < ∑ j : Fin (n + 1), (a j^2 + 1) := by positivity
example (a : ℕ → ℤ) : 0 < ∑ j in ({1} : Finset ℕ), (a j^2 + 1) := by
  have : Finset.Nonempty {1} := singleton_nonempty 1
  positivity

end Mathlib.Meta.Positivity

namespace Finset

open Function
open scoped BigOperators

variable {ι N : Type*} [OrderedCommMonoid N] {f g : ι → N} {s t : Finset ι}

@[to_additive sum_eq_zero_iff_of_nonpos]
lemma prod_eq_one_iff_of_le_one'' : (∀ i ∈ s, f i ≤ 1) → ((∏ i in s, f i) = 1 ↔ ∀ i ∈ s, f i = 1) :=
  @prod_eq_one_iff_of_one_le' _ Nᵒᵈ _ _ _

end Finset

namespace Finset
variable {α 𝕜 : Type*} [LinearOrderedCommRing 𝕜]

lemma sum_mul_sq_le_sq_mul_sq (s : Finset α) (f g : α → 𝕜) :
    (∑ i in s, f i * g i) ^ 2 ≤ (∑ i in s, f i ^ 2) * ∑ i in s, g i ^ 2 := by
  have h : 0 ≤ ∑ i in s, (f i * ∑ j in s, g j ^ 2 - g i * ∑ j in s, f j * g j) ^ 2 := by positivity
  simp_rw [sub_sq, sum_add_distrib, Finset.sum_sub_distrib, mul_pow, mul_assoc, ←mul_sum, ←
    sum_mul, mul_left_comm, ←mul_assoc, ←sum_mul, mul_right_comm, ←sq, mul_comm, sub_add,
    two_mul, add_sub_cancel, sq (∑ j in s, g j ^ 2), ←mul_assoc, ←mul_sub_right_distrib] at h
  obtain h' | h' := (sum_nonneg fun i _ ↦ sq_nonneg (g i)).eq_or_lt
  · have h'' : ∀ i ∈ s, g i = 0 := fun i hi ↦ by
      simpa using (sum_eq_zero_iff_of_nonneg fun i _ ↦ sq_nonneg (g i)).1 h'.symm i hi
    rw [←h', sum_congr rfl (show ∀ i ∈ s, f i * g i = 0 from fun i hi ↦ by simp [h'' i hi])]
    simp
  · rw [←sub_nonneg]
    exact nonneg_of_mul_nonneg_left h h'

end Finset
