import Mathlib.Data.Complex.Basic
import LeanAPAP.Prereqs.Expect.Basic
import LeanAPAP.Prereqs.NNRat.NNReal

open scoped BigOps NNReal NNRat

namespace NNReal
variable {ι : Type*}

@[simp, norm_cast]
lemma coe_expect (s : Finset ι) (a : ι → ℝ≥0) : 𝔼 i ∈ s, a i = 𝔼 i ∈ s, (a i : ℝ) :=
  map_expect toRealHom _ _

end NNReal

namespace Complex
variable {ι : Type*}

@[simp, norm_cast]
lemma ofReal_expect (s : Finset ι) (a : ι → ℝ) : 𝔼 i ∈ s, a i = 𝔼 i ∈ s, (a i : ℂ) :=
  map_expect ofReal _ _

end Complex

namespace IsROrC
variable {ι 𝕜 : Type*} [IsROrC 𝕜]

@[simp, norm_cast]
lemma coe_expect (s : Finset ι) (a : ι → ℝ) : 𝔼 i ∈ s, a i = 𝔼 i ∈ s, (a i : 𝕜) :=
  map_expect (algebraMap _ _) _ _

end IsROrC
