import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Positivity.Core

open Finset
namespace Mathlib.Meta.Positivity
open Qq Lean Meta

@[positivity Finset.card _]
def evalFinsetCard : PositivityExt where eval _ _ e := do
  let ⟨v, _l, _r⟩ ← inferTypeQ' <| (Expr.getAppArgs (← withReducible (whnf e))).get! 1
  let .app (.app _f (α : Q(Type v))) (s : Q(Finset $α)) ← withReducible (whnf e) | throwError "not `Finset.card`"

  let so : Option Q(Finset.Nonempty $s) ← do -- TODO: if I make a typo it doesn't complain?
    try {
      let _fi ← synthInstanceQ (q(Fintype $α) : Q(Type v))
      let _no ← synthInstanceQ (q(Nonempty $α) : Q(Prop))
      match s with
      | ~q(@univ _ $fi) => pure (some q(Finset.univ_nonempty (α := $α)))
      | _ => pure none }
    catch _e => do
      let .some fv ← findLocalDeclWithType? q(Finset.Nonempty $s) | pure none
      pure (some (.fvar fv))
  match so with
  | .some (fi : Q(Finset.Nonempty $s)) => do
    return .positive (q(@Finset.Nonempty.card_pos.{v} $α $s $fi) : Q(0 < Finset.card $s))
  | _ => pure .none

@[positivity Fintype.card _]
def evalFintypeCard : PositivityExt where eval _ _ e := do
  let .app (.app (.const _ [u]) (α : Q(Type u))) (fi : Q(Fintype $α)) ← withReducible (whnf e)
    | throwError "not `Fintype.card`"
  let no ← synthInstanceQ (q(Nonempty $α) : Q(Prop))
  pure (.positive (q(@Fintype.card_pos.{u} $α $fi $no) : Q(0 < Fintype.card $α)))

example {α : Type*} {s : Finset α} (hs : s.Nonempty) : 0 < s.card := by positivity
example {α : Type*} [Fintype α] [Nonempty α] : 0 < (univ : Finset α).card := by positivity
example {α : Type*} [Fintype α] [Nonempty α] : 0 < Fintype.card α := by positivity

end Mathlib.Meta.Positivity
