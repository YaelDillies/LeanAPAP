import Mathlib.Data.Real.Basic
import LeanAPAP.Prereqs.Expect.Basic

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
