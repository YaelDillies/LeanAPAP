import Mathlib.Data.Complex.BigOperators
import LeanAPAP.Mathlib.Algebra.BigOperators.Expect

open scoped BigOps

namespace Complex
variable {α : Type*} (s : Finset α)

@[simp, norm_cast]
lemma ofReal_expect (f : α → ℝ) : 𝔼 i ∈ s, f i = 𝔼 i ∈ s, (f i : ℂ) := map_expect ofReal _ _
