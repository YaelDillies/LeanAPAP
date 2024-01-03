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
