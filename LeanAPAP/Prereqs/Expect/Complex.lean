import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic

open Finset
open scoped BigOperators NNReal

section
variable {ι K E : Type*} [RCLike K] [NormedField E] [CharZero E] [NormedSpace K E]

include K in
@[bound]
lemma norm_expect_le {s : Finset ι} {f : ι → E} : ‖𝔼 i ∈ s, f i‖ ≤ 𝔼 i ∈ s, ‖f i‖ :=
  le_expect_of_subadditive norm_zero norm_add_le (fun _ _ ↦ by rw [RCLike.norm_nnqsmul K])

end

namespace NNReal
variable {ι : Type*}

@[simp, norm_cast]
lemma coe_expect (s : Finset ι) (f : ι → ℝ≥0) : 𝔼 i ∈ s, f i = 𝔼 i ∈ s, (f i : ℝ) :=
  map_expect toRealHom ..

end NNReal

namespace Complex
variable {ι : Type*}

@[simp, norm_cast]
lemma ofReal_expect (s : Finset ι) (f : ι → ℝ) : 𝔼 i ∈ s, f i = 𝔼 i ∈ s, (f i : ℂ) :=
  map_expect ofReal ..

end Complex

namespace RCLike
variable {ι 𝕜 : Type*} [RCLike 𝕜]

@[simp, norm_cast]
lemma coe_expect (s : Finset ι) (f : ι → ℝ) : 𝔼 i ∈ s, f i = 𝔼 i ∈ s, (f i : 𝕜) :=
  map_expect (algebraMap ..) ..

end RCLike
