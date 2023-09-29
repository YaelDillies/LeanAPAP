import Mathlib.Algebra.BigOperators.Basic
import LeanAPAP.Mathlib.Algebra.Group.Basic

/-!
## TODO

* More explicit arguments to `Finset.sum_attach`
-/

-- We use a custom namespace instead of `BigOperators` because we want to override the notation from
-- mathlib
namespace BigOps
open Std.ExtendedBinder Lean Meta

/-- `finset% t` elaborates `t` as a `Finset`.
If `t` is a `Set`, then inserts `Set.toFinset`.
Does not make use of the expected type; useful for big operators over finsets.
```
#check finset% Finset.range 2 -- Finset Nat
#check finset% (Set.univ : Set Bool) -- Finset Bool
```
-/
elab (name := finsetStx) "finset% " t:term : term => do
  let u ← mkFreshLevelMVar
  let ty ← mkFreshExprMVar (mkSort (.succ u))
  let x ← Elab.Term.elabTerm t (mkApp (.const ``Finset [u]) ty)
  let xty ← whnfR (← inferType x)
  if xty.isAppOfArity ``Set 1 then
    Elab.Term.elabAppArgs (.const ``Set.toFinset [u]) #[] #[.expr x] none false false
  else
    return x

open Lean.Elab.Term.Quotation in
/-- `quot_precheck` for the `finset%` syntax. -/
@[quot_precheck BigOperators.finsetStx] def precheckFinsetStx : Precheck
  | `(finset% $t) => precheck t
  | _ => Elab.throwUnsupportedSyntax

-- TODO: contribute this modification back to `extBinder`

/-- A `bigOpBinder` is like an `extBinder` and has the form `x`, `x : ty`, or `x pred`
where `pred` is a `binderPred` like `< 2`.
Unlike `extBinder`, `x` is a term. -/
syntax bigOpBinder := term:max ((" : " term) <|> binderPred)?
/-- A BigOperator binder in parentheses -/
syntax bigOpBinderParenthesized := " (" bigOpBinder ")"
/-- A list of parenthesized binders -/
syntax bigOpBinderCollection := bigOpBinderParenthesized+
/-- A single (unparenthesized) binder, or a list of parenthesized binders -/
syntax bigOpBinders := bigOpBinderCollection <|> (ppSpace bigOpBinder)

/-- Collects additional binder/Finset pairs for the given `bigOpBinder`.
Note: this is not extensible at the moment, unlike the usual `bigOpBinder` expansions. -/
def processBigOpBinder (processed : (Array (Term × Term)))
    (binder : TSyntax ``bigOpBinder) : MacroM (Array (Term × Term)) :=
  set_option hygiene false in
  withRef binder do
    match binder with
    | `(bigOpBinder| $x:term) =>
      match x with
      | `(($a + $b = $n)) => -- Maybe this is too cute.
        return processed |>.push (← `(⟨$a, $b⟩), ← `(Finset.Nat.antidiagonal $n))
      | _ => return processed |>.push (x, ← ``(Finset.univ))
    | `(bigOpBinder| $x : $t) => return processed |>.push (x, ← ``((Finset.univ : Finset $t)))
    | `(bigOpBinder| $x ∈ $s) => return processed |>.push (x, ← `(finset% $s))
    | `(bigOpBinder| $x < $n) => return processed |>.push (x, ← `(Finset.Iio $n))
    | `(bigOpBinder| $x ≤ $n) => return processed |>.push (x, ← `(Finset.Iic $n))
    | `(bigOpBinder| $x > $n) => return processed |>.push (x, ← `(Finset.Ioi $n))
    | `(bigOpBinder| $x ≥ $n) => return processed |>.push (x, ← `(Finset.Ici $n))
    | _ => Macro.throwUnsupported

/-- Collects the binder/Finset pairs for the given `bigOpBinders`. -/
def processBigOpBinders (binders : TSyntax ``bigOpBinders) :
    MacroM (Array (Term × Term)) :=
  match binders with
  | `(bigOpBinders| $b:bigOpBinder) => processBigOpBinder #[] b
  | `(bigOpBinders| $[($bs:bigOpBinder)]*) => bs.foldlM processBigOpBinder #[]
  | _ => Macro.throwUnsupported

/-- Collect the binderIdents into a `⟨...⟩` expression. -/
def bigOpBindersPattern (processed : (Array (Term × Term))) :
    MacroM Term := do
  let ts := processed.map Prod.fst
  if ts.size == 1 then
    return ts[0]!
  else
    `(⟨$ts,*⟩)

/-- Collect the terms into a product of sets. -/
def bigOpBindersProd (processed : (Array (Term × Term))) :
    MacroM Term := do
  if processed.isEmpty then
    `((Finset.univ : Finset Unit))
  else if processed.size == 1 then
    return processed[0]!.2
  else
    processed.foldrM (fun s p => `(SProd.sprod $(s.2) $p)) processed.back.2
      (start := processed.size - 1)

/--
- `∑ x, f x` is notation for `Finset.sum Finset.univ f`. It is the sum of `f x`,
  where `x` ranges over the finite domain of `f`.
- `∑ x ∈ s, f x` is notation for `Finset.sum s f`. It is the sum of `f x`,
  where `x` ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
- `∑ x ∈ s with p x, f x` is notation for `Finset.sum (Finset.filter p s) f`.
- `∑ (x ∈ s) (y ∈ t), f x y` is notation for `Finset.sum (s ×ˢ t) (fun ⟨x, y⟩ ↦ f x y)`.

These support destructuring, for example `∑ ⟨x, y⟩ ∈ s ×ˢ t, f x y`.

Notation: `"∑" bigOpBinders* ("with" term)? "," term` -/
scoped syntax (name := bigSum) "∑ " bigOpBinders ("with " term)? ", " term:67 : term

/--
- `∏ x, f x` is notation for `Finset.prod Finset.univ f`. It is the product of `f x`,
  where `x` ranges over the finite domain of `f`.
- `∏ x ∈ s, f x` is notation for `Finset.prod s f`. It is the product of `f x`,
  where `x` ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
- `∏ x ∈ s with p x, f x` is notation for `Finset.prod (Finset.filter p s) f`.
- `∏ (x ∈ s) (y ∈ t), f x y` is notation for `Finset.prod (s ×ˢ t) (fun ⟨x, y⟩ ↦ f x y)`.

These support destructuring, for example `∏ ⟨x, y⟩ ∈ s ×ˢ t, f x y`.

Notation: `"∏" bigOpBinders* ("with" term)? "," term` -/
scoped syntax (name := bigProd) "∏ " bigOpBinders ("with " term)? ", " term:67 : term

scoped macro_rules (kind := bigSum)
  | `(∑ $bs:bigOpBinders $[with $p?]?, $v) => do
    let processed ← processBigOpBinders bs
    let x ← bigOpBindersPattern processed
    let s ← bigOpBindersProd processed
    match p? with
    | some p => `(Finset.sum (Finset.filter (fun $x ↦ $p) $s) (fun $x ↦ $v))
    | none => `(Finset.sum $s (fun $x ↦ $v))

scoped macro_rules (kind := bigProd)
  | `(∏ $bs:bigOpBinders $[with $p?]?, $v) => do
    let processed ← processBigOpBinders bs
    let x ← bigOpBindersPattern processed
    let s ← bigOpBindersProd processed
    match p? with
    | some p => `(Finset.prod (Finset.filter (fun $x ↦ $p) $s) (fun $x ↦ $v))
    | none => `(Finset.prod $s (fun $x ↦ $v))

/-- (Deprecated, use `∑ x ∈ s, f x`)
`∑ x in s, f x` is notation for `Finset.sum s f`. It is the sum of `f x`,
where `x` ranges over the finite set `s`. -/
scoped syntax (name := bigsumin) "∑ " extBinder " in " term ", " term:67 : term
scoped macro_rules (kind := bigsumin)
  | `(∑ $x:ident in $s, $r) => `(∑ $x:ident ∈ $s, $r)
  | `(∑ $x:ident : $t in $s, $r) => `(∑ $x:ident ∈ ($s : Finset $t), $r)

/-- (Deprecated, use `∏ x ∈ s, f x`)
`∏ x in s, f x` is notation for `Finset.prod s f`. It is the product of `f x`,
where `x` ranges over the finite set `s`. -/
scoped syntax (name := bigprodin) "∏ " extBinder " in " term ", " term:67 : term
scoped macro_rules (kind := bigprodin)
  | `(∏ $x:ident in $s, $r) => `(∏ $x:ident ∈ $s, $r)
  | `(∏ $x:ident : $t in $s, $r) => `(∏ $x:ident ∈ ($s : Finset $t), $r)

open Lean Meta Parser.Term PrettyPrinter.Delaborator SubExpr
open Std.ExtendedBinder

/-- Delaborator for `Finset.prod`. The `pp.piBinderTypes` option controls whether
to show the domain type when the product is over `Finset.univ`. -/
@[scoped delab app.Finset.prod] def delabFinsetProd' : Delab := whenPPOption getPPNotation do
  let #[_, _, _, s, f] := (← getExpr).getAppArgs | failure
  guard $ f.isLambda
  let ppDomain ← getPPOption getPPPiBinderTypes
  let (i, body) ← withAppArg $ withBindingBodyUnusedName fun i => do
    return (i, ← delab)
  if s.isAppOfArity ``Finset.univ 2 then
    let binder ←
      if ppDomain then
        let ty ← withNaryArg 1 delab
        `(bigOpBinder| $(.mk i):ident : $ty)
      else
        `(bigOpBinder| $(.mk i):ident)
    `(∏ $binder:bigOpBinder, $body)
  else
    let ss ← withNaryArg 3 $ delab
    `(∏ $(.mk i):ident ∈ $ss, $body)

/-- Delaborator for `Finset.prod`. The `pp.piBinderTypes` option controls whether
to show the domain type when the sum is over `Finset.univ`. -/
@[scoped delab app.Finset.sum] def delabFinsetSum' : Delab := whenPPOption getPPNotation do
  let #[_, _, _, s, f] := (← getExpr).getAppArgs | failure
  guard $ f.isLambda
  let ppDomain ← getPPOption getPPPiBinderTypes
  let (i, body) ← withAppArg $ withBindingBodyUnusedName fun i => do
    return (i, ← delab)
  if s.isAppOfArity ``Finset.univ 2 then
    let binder ←
      if ppDomain then
        let ty ← withNaryArg 1 delab
        `(bigOpBinder| $(.mk i):ident : $ty)
      else
        `(bigOpBinder| $(.mk i):ident)
    `(∑ $binder:bigOpBinder, $body)
  else
    let ss ← withNaryArg 3 $ delab
    `(∑ $(.mk i):ident ∈ $ss, $body)

end BigOps

open scoped BigOps

namespace Finset
variable {α β γ : Type*} [CommMonoid β] {s s₁ s₂ : Finset α} {t : Finset γ} {f : α → β} {g : γ → β}

@[to_additive]
lemma prod_mul_prod_comm (f g h i : α → β) :
    (∏ a in s, f a * g a) * ∏ a in s, h a * i a = (∏ a in s, f a * h a) * ∏ a in s, g a * i a := by
  simp_rw [prod_mul_distrib, mul_mul_mul_comm]

@[to_additive]
lemma prod_nbij (i : α → γ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
    (i_inj : ∀ a₁ a₂, a₁ ∈ s → a₂ ∈ s → i a₁ = i a₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ∈ s, b = i a) : ∏ x in s, f x = ∏ x in t, g x :=
  prod_bij (λ a _ ↦ i a) hi h i_inj $ by simpa using i_surj

@[to_additive]
lemma prod_nbij' (i : α → γ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a)) (j : γ → α)
    (hj : ∀ a ∈ t, j a ∈ s) (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a) :
    ∏ x in s, f x = ∏ x in t, g x :=
  prod_bij' (λ a _ ↦ i a) hi h (λ b _ ↦ j b) hj left_inv right_inv

@[to_additive]
lemma prod_ite_one' (s : Finset α) (p : α → Prop) [DecidablePred p]
    (h : ∀ i, i ∈ s → ∀ j, j ∈ s → p i → p j → i = j) (a : β) :
    ∏ i in s, ite (p i) a 1 = ite (∃ i ∈ s, p i) a 1 :=
  prod_ite_one (λ i hi j hj ↦ by
    simpa only [Function.onFun_apply, Prop.disjoint_iff, not_imp_not, and_imp] using h i hi j hj) _

variable [DecidableEq α]

@[to_additive]
lemma prod_union_eq_left (hs : ∀ a ∈ s₂, a ∉ s₁ → f a = 1) :
    ∏ a in s₁ ∪ s₂, f a = ∏ a in s₁, f a :=
  Eq.symm $
    prod_subset (subset_union_left _ _) λ _a ha ha' ↦ hs _ ((mem_union.1 ha).resolve_left ha') ha'

@[to_additive]
lemma prod_union_eq_right (hs : ∀ a ∈ s₁, a ∉ s₂ → f a = 1) :
    ∏ a in s₁ ∪ s₂, f a = ∏ a in s₂, f a := by rw [union_comm, prod_union_eq_left hs]

@[to_additive (attr := simp)]
lemma prod_diag (s : Finset α) (f : α × α → β) : ∏ i in s.diag, f i = ∏ i in s, f (i, i) :=
  Eq.symm $
    prod_nbij (λ i ↦ (i, i)) (λ _i hi ↦ mem_diag.2 ⟨hi, rfl⟩) (λ _i _ ↦ rfl)
      (λ _i _j _ _ h ↦ (Prod.ext_iff.1 h).1) λ i hi ↦
      ⟨i.1, (mem_diag.1 hi).1, Prod.ext rfl (mem_diag.1 hi).2.symm⟩

end Finset

namespace Finset
variable {ι α : Type*} [DecidableEq ι] [CancelCommMonoid α] {s t : Finset ι} {f : ι → α}

@[to_additive]
lemma prod_sdiff_eq_prod_sdiff :
    ∏ i in s \ t, f i = ∏ i in t \ s, f i ↔ ∏ i in s, f i = ∏ i in t, f i :=
  eq_comm.trans $ eq_iff_eq_of_mul_eq_mul $ by
    rw [←prod_union disjoint_sdiff_self_left, ←prod_union disjoint_sdiff_self_left,
      sdiff_union_self_eq_union, sdiff_union_self_eq_union, union_comm]

@[to_additive]
lemma prod_sdiff_ne_prod_sdiff :
    ∏ i in s \ t, f i ≠ ∏ i in t \ s, f i ↔ ∏ i in s, f i ≠ ∏ i in t, f i :=
  prod_sdiff_eq_prod_sdiff.not

end Finset

open Finset

namespace Fintype
variable {α β : Type*} [Fintype α]

section CommMonoid
variable [CommMonoid β] (a : β)

@[to_additive]
lemma prod_ite_exists (p : α → Prop) [DecidablePred p] (h : ∀ i j, p i → p j → i = j) (a : β) :
    ∏ i, ite (p i) a 1 = ite (∃ i, p i) a 1 := by simp [prod_ite_one' univ p (by simpa using h)]

variable [DecidableEq α]

@[to_additive (attr := simp)]
lemma prod_dite_eq (a : α) (b : ∀ x, a = x → β) :
    (∏ x, if h : a = x then b x h else 1) = b a rfl := by simp

@[to_additive (attr := simp)]
lemma prod_dite_eq' (a : α) (b : ∀ x, x = a → β) :
    (∏ x, if h : x = a then b x h else 1) = b a rfl := by simp

@[to_additive (attr := simp)]
lemma prod_ite_eq (a : α) (b : α → β) : (∏ x, if a = x then b x else 1) = b a := by simp

@[to_additive (attr := simp)]
lemma prod_ite_eq' [DecidableEq α] (a : α) (b : α → β) : (∏ x, if x = a then b x else 1) = b a := by simp

end CommMonoid

variable [CommMonoidWithZero β] {p : α → Prop} [DecidablePred p]

lemma prod_boole : ∏ i, ite (p i) (1 : β) 0 = ite (∀ i, p i) 1 0 := by simp [Finset.prod_boole]

end Fintype
