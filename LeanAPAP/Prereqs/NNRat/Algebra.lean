import LeanAPAP.Prereqs.NNRat.Cast.CharZero

namespace NNRat

lemma den_mul_eq_num (q : ℚ≥0) : q.den * q = q.num := by
  rw [mul_comm, ← eq_div_iff (Nat.cast_ne_zero.2 q.den_pos.ne'), num_div_den]

lemma mul_den_eq_num (q : ℚ≥0) : q * q.den = q.num := by
  rw [← eq_div_iff (Nat.cast_ne_zero.2 q.den_pos.ne'), num_div_den]

end NNRat

open NNRat

variable {F α β : Type*}

section DivisionSemiring
variable [DivisionSemiring α] [CharZero α] [SMul ℚ≥0 α] [CompAction α]
  [DivisionSemiring β] [CharZero β] [SMul ℚ≥0 β] [CompAction β]

-- TODO: Do the `NNRat.cast` refactor to let this be an instance

instance NNRat.instAlgebra : Algebra ℚ≥0 α where
  smul_def' := smul_def
  toRingHom := NNRat.castHom α
  commutes' := NNRat.cast_commute

instance NNRat.instlinearMapClass [RingHomClass F α β] : LinearMapClass F ℚ≥0 α β where
  map_smulₛₗ f q a := by simp [NNRat.smul_def, NNRat.cast_id]; exact Or.inl q.num_div_den.symm

end DivisionSemiring

section Semifield
variable [Semifield β] [CharZero β] [SMul ℚ≥0 β] [CompAction β] [SMul α β]

instance NNRat.instSMulCommClass [SMulCommClass α β β] : SMulCommClass ℚ≥0 α β where
  smul_comm q a b := by simp [NNRat.smul_def, mul_smul_comm]

instance NNRat.instSMulCommClass' [SMulCommClass β α β] : SMulCommClass α ℚ≥0 β :=
  have := SMulCommClass.symm β α β
  SMulCommClass.symm _ _ _

end Semifield

section Semifield
variable [Semifield α] [CharZero α] [SMul ℚ≥0 α] [CompAction α] [Semiring β] [CharZero β]
  [NNRatCast β] [Module ℚ≥0 β] [CompAction β]

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
