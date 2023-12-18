import LeanAPAP.Prereqs.Expect.Basic
import Mathlib.Data.Complex.Basic

open scoped BigOps

namespace Complex
variable {ι : Type*}

@[simp, norm_cast]
lemma ofReal_expect (s : Finset ι) (a : ι → ℝ) : 𝔼 i ∈ s, a i = 𝔼 i ∈ s, (a i : ℂ) :=
  map_expect ofReal _ _

end Complex
