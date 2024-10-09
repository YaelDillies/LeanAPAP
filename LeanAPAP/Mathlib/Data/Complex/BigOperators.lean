import Mathlib.Data.Complex.BigOperators

open Fintype

namespace Complex
variable {ι : Type*}

@[simp] lemma ofReal'_comp_balance [Fintype ι] (f : ι → ℝ) :
    ofReal' ∘ balance f = balance (ofReal' ∘ f) := ofReal_comp_balance _

end Complex
