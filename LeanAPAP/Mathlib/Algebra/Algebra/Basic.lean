import Mathlib.Algebra.Algebra.Basic
import LeanAPAP.Mathlib.Data.Rat.Cast.Lemmas

open NNRat

variable {F α β : Type*}

section DivisionSemiring
variable [DivisionSemiring α] [CharZero α] [DivisionSemiring β] [CharZero β]

instance NNRat.instAlgebra : Algebra ℚ≥0 α where
  smul_def' := smul_def
  toRingHom := castHom α
  commutes' := cast_commute

instance NNRat.instlinearMapClass [FunLike F α β] [RingHomClass F α β] :
    LinearMapClass F ℚ≥0 α β where
  map_smulₛₗ f q a := by simp [smul_def, cast_id]

end DivisionSemiring

section Semifield
variable [Semifield β] [CharZero β] [SMul α β]

instance NNRat.instSMulCommClass [SMulCommClass α β β] : SMulCommClass ℚ≥0 α β where
  smul_comm q a b := by simp [smul_def, mul_smul_comm]

instance NNRat.instSMulCommClass' [SMulCommClass β α β] : SMulCommClass α ℚ≥0 β :=
  have := SMulCommClass.symm β α β
  SMulCommClass.symm _ _ _

end Semifield

section Semifield
variable [Semifield α] [CharZero α] [Semiring β] [CharZero β] [NNRatCast β] [Module ℚ≥0 β]

variable (α) in
-- TODO: Change `nnsmul_eq_smul_cast` to match
/-- `nnqsmul` is equal to any other module structure via a cast. -/
lemma _root_.nnratCast_smul_eq_nnqsmul [Module α β] (q : ℚ≥0) (a : β) : (q : α) • a = q • a := by
  refine MulAction.injective₀ (α := ℚ≥0) (Nat.cast_ne_zero.2 q.den_pos.ne') ?_
  dsimp
  rw [← mul_smul, den_mul_eq_num, ← nsmul_eq_smul_cast, ← nsmul_eq_smul_cast, ← smul_assoc,
    nsmul_eq_mul q.den, ← cast_natCast, ←cast_mul, den_mul_eq_num, cast_natCast,
    ← nsmul_eq_smul_cast]

end Semifield
