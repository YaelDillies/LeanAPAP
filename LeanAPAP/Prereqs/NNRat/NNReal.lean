import Mathlib.Data.Real.NNReal
import LeanAPAP.Prereqs.NNRat.Algebra

open scoped NNRat NNReal

noncomputable instance : SMul ℚ≥0 ℝ≥0 where
  smul q r := q * r

instance : CompAction ℝ≥0 where
  nnqsmul_eq_mul' _ _ := rfl
