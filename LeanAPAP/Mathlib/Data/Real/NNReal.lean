import Mathlib.Data.Real.NNReal

open scoped NNReal

namespace NNReal
variable {x : ℝ≥0}

instance {M : Type*} [OrderedAddCommMonoid M] [Module ℝ M] [OrderedSMul ℝ M] :
    OrderedSMul ℝ≥0 M where
  smul_lt_smul_of_pos hab hc := (smul_lt_smul_of_pos_left hab (NNReal.coe_pos.2 hc) : _)
  lt_of_smul_lt_smul_of_pos {a b c} hab _ :=
    lt_of_smul_lt_smul_of_nonneg_left (by exact hab) (NNReal.coe_nonneg c)

end NNReal
