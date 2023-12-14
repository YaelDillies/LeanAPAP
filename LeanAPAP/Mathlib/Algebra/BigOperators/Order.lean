import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Ring

open scoped BigOperators

namespace Finset
variable {α 𝕜 : Type*} [LinearOrderedCommRing 𝕜]

lemma sum_mul_sq_le_sq_mul_sq (s : Finset α) (f g : α → 𝕜) :
    (∑ i in s, f i * g i) ^ 2 ≤ (∑ i in s, f i ^ 2) * ∑ i in s, g i ^ 2 := by
  have h : 0 ≤ ∑ i in s, (f i * ∑ j in s, g j ^ 2 - g i * ∑ j in s, f j * g j) ^ 2 :=
    sum_nonneg fun i _ ↦ sq_nonneg _
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

open Finset
open scoped BigOperators
open Qq Lean Meta

-- TODO: This doesn't handle universe-polymorphic input
@[positivity Finset.sum _ _]
def Mathlib.Meta.Positivity.evalFinsetSum : PositivityExt where eval {u β2} zβ pβ e := do
  let .app (.app (.app (.app (.app (.const _ [_, v]) (β : Q(Type u))) (α : Q(Type v)))
    (_a : Q(AddCommMonoid $β))) (s : Q(Finset $α))) (b : Q($α → $β)) ← withReducible (whnf e)
      | throwError "not `Finset.sum`"
  haveI' : $β =Q $β2 := ⟨⟩
  haveI' : $e =Q Finset.sum $s $b := ⟨⟩
  let (lhs, _, (rhs : Q($β))) ← lambdaMetaTelescope b
  let rb ← core zβ pβ rhs

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
  match rb, so with
  | .nonnegative pb, _ => do
    let pα' ← synthInstanceQ (q(OrderedAddCommMonoid $β) : Q(Type u))
    assertInstancesCommute
    let pr : Q(∀ (i : $α), 0 ≤ $b i) ← mkLambdaFVars lhs pb
    pure (.nonnegative q(@sum_nonneg.{u, v} $α $β $pα' $b $s (fun i _h => $pr i)))
  | .positive pb, .some (fi : Q(Finset.Nonempty $s)) => do
    let pα' ← synthInstanceQ (q(OrderedCancelAddCommMonoid $β) : Q(Type u))
    assertInstancesCommute
    let pr : Q(∀ (i : $α), 0 < $b i) ← mkLambdaFVars lhs pb
    pure (.positive q(@sum_pos.{u, v} $α $β $pα' $b $s (fun i _h => $pr i) $fi))
  | _, _ => pure .none

example (n : ℕ) (a : ℕ → ℤ) : 0 ≤ ∑ j in range n, a j^2 := by positivity
example (a : ULift.{2} ℕ → ℤ) (s : Finset (ULift.{2} ℕ)) : 0 ≤ ∑ j in s, a j^2 := by positivity
example (n : ℕ) (a : ℕ → ℤ) : 0 ≤ ∑ j : Fin 8, ∑ i in range n, (a j^2 + i ^ 2) := by positivity
example (n : ℕ) (a : ℕ → ℤ) : 0 < ∑ j : Fin (n + 1), (a j^2 + 1) := by positivity
example (a : ℕ → ℤ) : 0 < ∑ j in ({1} : Finset ℕ), (a j^2 + 1) := by
  have : Finset.Nonempty {1} := singleton_nonempty 1
  positivity
