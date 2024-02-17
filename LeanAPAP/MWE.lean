import Mathlib.Tactic.Positivity.Core

section IsFun
open Lean Elab Tactic Term Meta PrettyPrinter Qq

def isFun {u : Level} (π : Q(Type $u)) : MetaM (Option (Σ v w : Level, Q(Type v) × Q(Type w))) := do
  let v ← mkFreshLevelMVar
  let w ← mkFreshLevelMVar
  withNewMCtxDepth (allowLevelAssignments := true) do
    let α ← mkFreshExprMVar (some (.sort (.succ v)))
    let β ← mkFreshExprMVar (some (.sort (.succ w)))
    match ← withReducible (isDefEq (.forallE .anonymous α β .default) π) with
    | true => pure (some ⟨v, w, ← instantiateMVars α, ← instantiateMVars β⟩)
    | false => pure none

end IsFun

section Defs
variable {α β : Type*}

def conv (f g : α → β) : α → β := sorry

variable [OrderedAddCommMonoid β] {f g : α → β}

lemma conv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ conv f g := sorry
lemma conv_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ conv f g := conv_nonneg hf.le hg
lemma conv_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ conv f g := conv_nonneg hf hg.le
lemma conv_pos (hf : 0 < f) (hg : 0 < g) : 0 < conv f g := sorry

end Defs

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

@[positivity conv _ _] def evalConv : PositivityExt where eval {u π} zπ pπ e := do
  let .some ⟨v, w, ~q($α), ~q($β)⟩ ← isFun π | throwError "not `conv`"
  have : u =QL max v w := ⟨⟩
  have : $π =Q ($α → $β) := ⟨⟩
  match q($e) with
  | ~q(@conv $α $β $f $g) => do
    let _ ← synthInstanceQ q(OrderedAddCommMonoid $β)
    let _ ← synthInstanceQ q(PartialOrder $β)
    match ← core q(inferInstance) q(inferInstance) f with
    | .positive rf => do
      match ← core q(inferInstance) q(inferInstance) g with
      | .positive rg => do
        let rf : Q(0 < $f) := rf
        let rg : Q(0 < $g) := rg
/-
application type mismatch
  conv_pos «$rf»
argument
  «$rf»
has type
  @OfNat.ofNat («$α» → «$β») 0
      (@Zero.toOfNat0 («$α» → «$β») (@Pi.instZero «$α» (fun a ↦ «$β») fun i ↦ AddMonoid.toZero)) <
    «$f» : Prop
but is expected to have type
  @OfNat.ofNat («$α» → «$β») 0
      (@Zero.toOfNat0 («$α» → «$β») (@Pi.instZero «$α» (fun a ↦ «$β») fun i ↦ AddMonoid.toZero)) <
    ?m.21991 : Prop
-/
        return .positive q(@conv_pos $α $β _ _ _ $rf $rg)
      | .nonnegative rg => sorry
      | _ => return .none
    | .nonnegative rf => sorry
    | _ => return .none
  | _ => throwError "not `conv`"

end Mathlib.Meta.Positivity

section Examples
variable {α β : Type*} [OrderedAddCommMonoid β] {f g : α → β}

example (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ conv f g := by positivity
example (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ conv f g := by positivity
example (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ conv f g := by positivity
example (hf : 0 < f) (hg : 0 < g) : 0 < conv f g := by positivity

end Examples
