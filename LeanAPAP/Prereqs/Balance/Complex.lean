import Mathlib.Algebra.BigOperators.Balance
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.BigOperators

open Fintype
open scoped NNReal

namespace Complex
variable {ι : Type*}

@[simp] lemma ofReal_comp_balance [Fintype ι] (f : ι → ℝ) :
    ofReal ∘ balance f = balance (ofReal ∘ f) := by simp [balance]

@[simp] lemma ofReal'_comp_balance [Fintype ι] (f : ι → ℝ) :
    ofReal' ∘ balance f = balance (ofReal' ∘ f) := ofReal_comp_balance _

end Complex

namespace RCLike
variable {ι 𝕜 : Type*} [RCLike 𝕜] [Fintype ι] (f : ι → ℝ) (a : ι)

@[simp, norm_cast]
lemma coe_balance : (↑(balance f a) : 𝕜) = balance ((↑) ∘ f) a := map_balance (algebraMap ..) ..

@[simp] lemma coe_comp_balance : ((↑) : ℝ → 𝕜) ∘ balance f = balance ((↑) ∘ f) :=
  funext $ coe_balance _

@[simp] lemma ofReal_comp_balance : ofReal ∘ balance f = balance (ofReal ∘ f : ι → 𝕜) := by
  simp [balance]

end RCLike
