import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Real
variable {x : ℝ}

lemma le_log_one_add_inv (hx : 0 < x) : (1 + x)⁻¹ ≤ log (1 + x⁻¹) := by
  have' := log_le_sub_one_of_pos (x := (1 + x⁻¹)⁻¹) (by positivity)
  rw [log_inv, neg_le] at this
  exact this.trans' (by field_simp [add_comm])

end Real

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function Real NormNum Nat Sum3

section
variable {R : Type*} {e : R} {n : ℕ}

private lemma le_one_of_isNat [StrictOrderedSemiring R] (h : IsNat e n) (w : ble 1 n = true) :
    1 ≤ (e : R) := by simpa [h.to_eq rfl] using w

private lemma lt_one_of_isNat [StrictOrderedSemiring R] (h : IsNat e n) (w : ble 2 n = true) :
    1 < (e : R) := by simpa [h.to_eq rfl] using w

private lemma ne_one_of_isNegNat [StrictOrderedRing R] (h : IsInt e (.negOfNat n)) :
    (e : R) ≠ 1 := by
  rw [h.neg_to_eq rfl]; exact ((neg_nonpos.2 n.cast_nonneg).trans_lt zero_lt_one).ne

private lemma lt_one_of_isRat {n : ℤ} {d : ℕ} [LinearOrderedRing R] :
    IsRat e n d → decide (d < n) → 1 < e := by
  rintro ⟨inv, rfl⟩ h
  refine one_lt_of_lt_mul_right₀ d.cast_nonneg ?_
  rw [mul_assoc, invOf_mul_self, mul_one]
  exact mod_cast of_decide_eq_true h

private lemma le_one_of_isRat {n : ℤ} {d : ℕ} [LinearOrderedRing R] :
    IsRat e n d → decide (d ≤ n) → 1 ≤ e := by
  rintro ⟨inv, rfl⟩ h
  refine one_le_of_le_mul_right₀ (d.cast_nonneg.lt_of_ne' inv.ne_zero) ?_
  rw [mul_assoc, invOf_mul_self, mul_one]
  exact mod_cast of_decide_eq_true h

private lemma ne_one_of_isRat {n : ℤ} {d : ℕ} [LinearOrderedRing R] :
    IsRat e n d → decide (n ≠ d) → e ≠ 1 := by
  rintro ⟨inv, rfl⟩ h
  refine (mul_eq_right₀ inv.ne_zero).ne.1 ?_
  rw [mul_assoc, invOf_mul_self, mul_one]
  exact mod_cast of_decide_eq_true h

end

variable {u : Level} {α : Q(Type u)} (oα : Q(One $α)) (pα : Q(PartialOrder $α))

/-- Attempts to prove a `Strictness` result when `e` evaluates to a literal number. -/
def normNumOne (e : Q($α)) : MetaM (Option (Q(1 < $e) ⊕ Q(1 ≤ $e) ⊕ Q($e ≠ 1))) := do
  match ← NormNum.derive e with
  | .isBool .. => pure none
  | .isNat _ lit p =>
    if 0 < lit.natLit! then
      let _a ← synthInstanceQ q(StrictOrderedSemiring $α)
      assumeInstancesCommute
      have p : Q(NormNum.IsNat $e $lit) := p
      haveI' p' : Nat.ble 2 $lit =Q true := ⟨⟩
      pure $ some $ in₀ q(lt_one_of_isNat $p $p')
    else
      let _a ← synthInstanceQ q(StrictOrderedSemiring $α)
      assumeInstancesCommute
      have p : Q(NormNum.IsNat $e $lit) := p
      haveI' p' : Nat.ble 1 $lit =Q true := ⟨⟩
      pure $ some $ in₁ q(le_one_of_isNat $p $p')
  | .isNegNat _ lit p =>
    let _a ← synthInstanceQ q(StrictOrderedRing $α)
    assumeInstancesCommute
    have p : Q(NormNum.IsInt $e (Int.negOfNat $lit)) := p
    haveI' p' : Nat.ble 1 $lit =Q true := ⟨⟩
    pure $ some $ in₂ q(ne_one_of_isNegNat $p)
  | .isRat _i q n d p =>
    let _a ← synthInstanceQ q(LinearOrderedRing $α)
    assumeInstancesCommute
    have p : Q(NormNum.IsRat $e $n $d) := p
    if 0 < q then
      haveI' w : decide ($d < $n) =Q true := ⟨⟩
      pure $ some $ .inl q(lt_one_of_isRat $p $w)
    else if q = 0 then -- should not be reachable, but just in case
      haveI' w : decide ($d ≤ $n) =Q true := ⟨⟩
      pure $ some $ in₁ q(le_one_of_isRat $p $w)
    else
      haveI' w : decide ($n ≠ $d) =Q true := ⟨⟩
      pure $ some $ in₂ q(ne_one_of_isRat $p $w)

/-- A variation on `assumption` which checks if the hypothesis `ldecl` is `a [</≤/=] e`
where `a` is a numeral. -/
def compareHypOne (e : Q($α)) (ldecl : LocalDecl) :
    MetaM (Option (Q(1 < $e) ⊕ Q(1 ≤ $e) ⊕ Q($e ≠ 1))) := do
  have e' : Q(Prop) := ldecl.type
  let p : Q($e') := .fvar ldecl.fvarId
  match e' with
  | ~q(@LE.le.{u} $β $_le $lo $hi) =>
    let .defEq (_ : $α =Q $β) ← isDefEqQ α β | return none
    let .defEq _ ← isDefEqQ e hi | return none
    assertInstancesCommute
    match lo with
    | ~q(1) => pure $ some $ .inr $ .inl q($p)
    | _ =>
      match ← normNumOne oα pα lo with
      | some $ in₀ p₁ => pure $ some $ in₀ q(lt_of_lt_of_le $p₁ $p)
      | some $ in₁ p₁ => pure $ some $ in₁ q(le_trans $p₁ $p)
      | _ => return none
  | ~q(@LT.lt.{u} $β $_lt $lo $hi) =>
    let .defEq (_ : $α =Q $β) ← isDefEqQ α β | return none
    let .defEq _ ← isDefEqQ e hi | return none
    assertInstancesCommute
    match lo with
    | ~q(1) => pure $ some $ in₀ q($p)
    | _ =>
      match ← normNumOne oα pα lo with
      | some $ in₀ p₁ => pure $ some $ in₀ q(lt_trans $p₁ $p)
      | some $ in₁ p₁ => pure $ some $ in₀ q(lt_of_le_of_lt $p₁ $p)
      | _ => return none
  | ~q(@Eq.{u+1} $α' $lhs $rhs) =>
    let .defEq (_ : $α =Q $α') ← isDefEqQ α α' | return none
    match ← isDefEqQ e rhs with
    | .defEq _ =>
      match lhs with
      | ~q(1) => pure $ some $ in₁ q(le_of_eq $p)
      | _ =>
        match ← normNumOne oα pα lhs with
        | some $ in₀ p₁ => pure $ some $ in₀ q(lt_of_lt_of_eq $p₁ $p)
        | some $ in₁ p₁ => pure $ some $ in₁ q(le_of_le_of_eq $p₁ $p)
        | some $ in₂ p₁ => pure $ some $ in₂ q(ne_of_ne_of_eq' $p₁ $p)
        | none => pure none
    | .notDefEq =>
      let .defEq _ ← isDefEqQ e lhs | return none
      match rhs with
      | ~q(1) => pure $ some $ in₁ q(ge_of_eq $p)
      | _ =>
        assertInstancesCommute
        match ← normNumOne oα pα rhs with
        | some $ in₀ p₁ => pure $ some $ in₀ q(lt_of_lt_of_eq $p₁ $ Eq.symm $p)
        | some $ in₁ p₁ => pure $ some $ in₁ q(le_of_le_of_eq $p₁ $ Eq.symm $p)
        | some $ in₂ p₁ => pure $ some $ in₂ q(ne_of_ne_of_eq' $p₁ $ Eq.symm $p)
        | none => pure none
  | ~q(@Ne.{u + 1} $α' $lhs $rhs) =>
    let .defEq (_ : $α =Q $α') ← isDefEqQ α α' | return none
    match lhs, rhs with
    | ~q(1), _ =>
      let .defEq _ ← isDefEqQ e rhs | return none
      pure $ some $ in₂ q(Ne.symm $p)
    | _, ~q(1) =>
      let .defEq _ ← isDefEqQ e lhs | return none
      pure $ some $ in₂ p
    | _, _ => return none
  | _ => return none

variable {oα pα} in
def orElseOne {e : Q($α)} (t₁ : Option (Q(1 < $e) ⊕ Q(1 ≤ $e) ⊕ Q($e ≠ 1)))
    (t₂ : MetaM (Option (Q(1 < $e) ⊕ Q(1 ≤ $e) ⊕ Q($e ≠ 1)))) :
    MetaM (Option (Q(1 < $e) ⊕ Q(1 ≤ $e) ⊕ Q($e ≠ 1))) := do
  match t₁ with
  | none => t₂
  | p@(some $ in₀ _) => pure p
  | some $ in₁ p₁ =>
    match ← t₂ with
    | p@(some $ in₀ _) => pure p
    | some $ in₂ p₂ => pure $ some $ in₀ q(lt_of_le_of_ne' $p₁ $p₂)
    | _ => pure $ some $ in₁ p₁
  | some $ in₂ p₁ =>
    match ← t₂ with
    | p@(some $ in₀ _) => pure p
    | some $ in₁ p₂ => pure $ some $ in₀ q(lt_of_le_of_ne' $p₂ $p₁)
    | _ => pure $ some $ in₂ p₁

/-- Extension for the `positivity` tactic: `Nat.cast` is always non-negative,
and positive when its input is. -/
@[positivity Real.log _] def evalRealLog : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(log $a) =>
    let mut ra ← normNumOne q(inferInstance) q(inferInstance) a
    for ldecl in ← getLCtx do
      if !ldecl.isImplementationDetail then
        ra ← orElseOne ra <| compareHypOne q(inferInstance) q(inferInstance) a ldecl
    assertInstancesCommute
    match ra with
    | some $ in₀ pa => pure $ .positive q(Real.log_pos $pa)
    | some $ in₁ pa => pure $ .nonnegative q(Real.log_nonneg $pa)
    | _ => pure .none
  | _, _, _ => throwError "not `Real.log`"

-- example {x : ℝ} (hx : 1 ≤ x) : 0 ≤ log x := by positivity
-- example {x : ℝ} (hx : 1 < x) : 0 < log x := by positivity

end Mathlib.Meta.Positivity
