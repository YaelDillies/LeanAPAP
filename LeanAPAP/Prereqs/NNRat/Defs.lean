import Mathlib.Data.NNRat.Defs

open scoped NNRat

/-- Type class for the canonical homomorphism `ℚ≥0 → α`. -/
class NNRatCast (α : Type*) :=
  /-- The canonical homomorphism `ℚ≥0 → α`. -/
  nnratCast : ℚ≥0 → α

variable {α : Type*}

/-- Canonical homomorphism from `ℚ≥0` to a division semiring `α`.

This is just the bare function in order to aid in creating instances of `DivisionSemiring`. -/
@[coe, reducible, match_pattern]
protected def NNRat.cast [NNRatCast α] : ℚ≥0 → α := NNRatCast.nnratCast

-- See note [coercion into rings]
instance NNRatCast.toCoeTail [NNRatCast α] : CoeTail ℚ≥0 α where coe := NNRat.cast

-- See note [coercion into rings]
instance NNRatCast.CoeHTCT [NNRatCast α] : CoeHTCT ℚ≥0 α where coe := NNRat.cast

instance NNRat.instNNRatCast : NNRatCast ℚ≥0 where nnratCast q := q
