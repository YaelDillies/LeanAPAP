import Mathlib.Algebra.Order.SMul

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

-- /-- The `positivity` extension which identifies expressions of the form `a • b`,
-- such that `positivity` successfully recognises both `a` and `b`. -/
-- @[positivity _ • _, SMul.smul _ _] def evalSMul : PositivityExt where eval {u α} zα pα e := do
--   let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← withReducible (whnf e)
--     | throwError "not •"
--   let _e_eq : $e =Q $f $a $b := ⟨⟩
--   let _a ← synthInstanceQ q(StrictOrderedSemiring $α)
--   assumeInstancesCommute
--   let ⟨_f_eq⟩ ← withDefault <| withNewMCtxDepth <| assertDefEqQ (u := u.succ) f q(HMul.hMul)
--   let ra ← core zα pα a; let rb ← core zα pα b
--   match ra, rb with
--   | .positive pa, .positive pb => pure (.positive q(mul_pos $pa $pb))
--   | .positive pa, .nonnegative pb => pure (.nonnegative q(mul_nonneg_of_pos_of_nonneg $pa $pb))
--   | .nonnegative pa, .positive pb => pure (.nonnegative q(mul_nonneg_of_nonneg_of_pos $pa $pb))
--   | .nonnegative pa, .nonnegative pb => pure (.nonnegative q(mul_nonneg $pa $pb))
--   | .positive pa, .nonzero pb =>
--     let _a ← synthInstanceQ (q(NoZeroDivisors $α) : Q(Prop))
--     pure (.nonzero q(mul_ne_zero_of_pos_of_ne_zero $pa $pb))
--   | .nonzero pa, .positive pb =>
--     let _a ← synthInstanceQ (q(NoZeroDivisors $α) : Q(Prop))
--     pure (.nonzero q(mul_ne_zero_of_ne_zero_of_pos $pa $pb))
--   | .nonzero pa, .nonzero pb =>
--     let _a ← synthInstanceQ (q(NoZeroDivisors $α) : Q(Prop))
--     pure (.nonzero (q(mul_ne_zero $pa $pb)))
--   | _, _ => pure .none

-- example {a : ℤ} {b : ℚ} (ha : 0 < a) (hb : 0 < b) : 0 < a • b := by positivity
-- example {a : ℤ} {b : ℚ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a • b := by positivity
-- example {a : ℤ} {b : ℚ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a • b := by positivity
-- example {a : ℤ} {b : ℚ} (ha : 0 < a) (hb : b ≠ 0) : a • b ≠ 0 := by positivity
-- example {a : ℤ} {b : ℚ} (ha : a ≠ 0) (hb : 0 < b) : a • b ≠ 0 := by positivity
-- example {a : ℤ} {b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : a • b ≠ 0 := by positivity

end Mathlib.Meta.Positivity
