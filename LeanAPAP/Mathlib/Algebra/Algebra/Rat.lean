import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Basic

variable {α β : Type*}

instance [Monoid α] [AddCommMonoid β] [Module ℚ≥0 β] [DistribMulAction α β] :
    SMulCommClass ℚ≥0 α β where
  smul_comm q a b := by
    rw [← q.num_div_den, div_eq_mul_inv]
    simp_rw [mul_smul, inv_natCast_smul_comm, Nat.cast_smul_eq_nsmul]
    rw [smul_comm a q.num]

instance [Monoid α] [AddCommMonoid β] [Module ℚ≥0 β] [DistribMulAction α β] :
    SMulCommClass α ℚ≥0 β := .symm ..

instance [Semiring α] [Module ℚ≥0 α] : IsScalarTower ℚ≥0 α α where
  smul_assoc q a b := sorry

instance [Monoid α] [AddCommGroup β] [Module ℚ β] [DistribMulAction α β] :
    SMulCommClass ℚ α β where
  smul_comm q a b := by
    rw [← q.num_div_den, div_eq_mul_inv]
    simp_rw [mul_smul, inv_natCast_smul_comm, Int.cast_smul_eq_zsmul]
    rw [smul_comm a q.num]

instance [Monoid α] [AddCommGroup β] [Module ℚ β] [DistribMulAction α β] : SMulCommClass α ℚ β :=
  .symm ..

instance [Ring α] [Module ℚ α] : IsScalarTower ℚ α α where
  smul_assoc q a b := sorry
