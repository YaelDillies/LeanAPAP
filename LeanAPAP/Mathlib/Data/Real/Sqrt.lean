import Mathlib.Data.Real.Sqrt

open Finset
open scoped BigOperators

namespace Real
variable {ι : Type*} {f g : ι → ℝ}

-- TODO: `NNReal` version
/-- Square root version of the **Cauchy-Schwarz inequality**. -/
lemma sum_sqrt_mul_sqrt_le (s : Finset ι) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i in s, sqrt (f i) * sqrt (g i) ≤ sqrt (∑ i in s, f i) * sqrt (∑ i in s, g i) := by
  simpa [*] using Finset.sum_mul_le_sqrt_mul_sqrt _ (fun x ↦ sqrt (f x)) (fun x ↦ sqrt (g x))

end Real
