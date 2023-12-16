import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Positivity.Core

open Finset
namespace Mathlib.Meta.Positivity
open Qq Lean Meta

@[positivity Finset.card _]
def evalFinsetCard : PositivityExt where eval {u α} _ _ e := do
  if let 0 := u then -- lean4#3060 means we can't combine this with the match below
    match α, e with
    | ~q(ℕ), ~q(@Finset.card $β $s) =>
      let so : Option Q(Finset.Nonempty $s) ← do -- TODO: It doesn't complain if we make a typo?
        try
          let _fi ← synthInstanceQ q(Fintype $β)
          let _no ← synthInstanceQ q(Nonempty $β)
          match s with
          | ~q(@univ _ $fi) => pure (some q(Finset.univ_nonempty (α := $β)))
          | _ => pure none
        catch _ => do
          let .some fv ← findLocalDeclWithType? q(Finset.Nonempty $s) | pure none
          pure (some (.fvar fv))
      assumeInstancesCommute
      match so with
      | .some (fi : Q(Finset.Nonempty $s)) => return .positive q(Finset.Nonempty.card_pos $fi)
      | _ => return .none
    | _, _ => throwError "not Finset.card"
  else throwError "not Finset.card"

@[positivity Fintype.card _]
def evalFintypeCard : PositivityExt where eval {u α} _ _ e := do
  if let 0 := u then -- lean4#3060 means we can't combine this with the match below
    match α, e with
    | ~q(ℕ), ~q(@Fintype.card $β $instβ) =>
      let instβno ← synthInstanceQ (q(Nonempty $β) : Q(Prop))
      assumeInstancesCommute
      return .positive q(@Fintype.card_pos $β $instβ $instβno)
    | _, _ => throwError "not Fintype.card"
  else throwError "not Fintype.card"

example {α : Type*} {s : Finset α} (hs : s.Nonempty) : 0 < s.card := by positivity
example {α : Type*} [Fintype α] [Nonempty α] : 0 < (univ : Finset α).card := by positivity
example {α : Type*} [Fintype α] [Nonempty α] : 0 < Fintype.card α := by positivity

end Mathlib.Meta.Positivity
