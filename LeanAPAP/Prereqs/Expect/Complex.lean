import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import LeanAPAP.Prereqs.Expect.Basic

open Finset
open scoped BigOperators NNReal

section
variable {ι K E : Type*} [RCLike K] [NormedField E] [CharZero E] [NormedSpace K E]

include K in
@[bound]
lemma norm_expect_le {s : Finset ι} {f : ι → E} : ‖𝔼 i ∈ s, f i‖ ≤ 𝔼 i ∈ s, ‖f i‖ :=
  s.le_expect_of_subadditive norm norm_zero norm_add_le (fun _ _ ↦ by rw [RCLike.norm_nnqsmul K]) f

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

@[simp] lemma ofReal_comp_balance [Fintype ι] (f : ι → ℝ) :
    ofReal ∘ balance f = balance (ofReal ∘ f) := by simp [balance]

@[simp] lemma ofReal'_comp_balance [Fintype ι] (f : ι → ℝ) :
    ofReal' ∘ balance f = balance (ofReal' ∘ f) := ofReal_comp_balance _

end Complex

namespace RCLike
variable {ι 𝕜 : Type*} [RCLike 𝕜]

@[simp, norm_cast]
lemma coe_expect (s : Finset ι) (f : ι → ℝ) : 𝔼 i ∈ s, f i = 𝔼 i ∈ s, (f i : 𝕜) :=
  map_expect (algebraMap ..) ..

variable [Fintype ι] (f : ι → ℝ) (a : ι)

@[simp, norm_cast]
lemma coe_balance : (↑(balance f a) : 𝕜) = balance ((↑) ∘ f) a := map_balance (algebraMap ..) ..

@[simp] lemma coe_comp_balance : ((↑) : ℝ → 𝕜) ∘ balance f = balance ((↑) ∘ f) :=
  funext $ coe_balance _

@[simp] lemma ofReal_comp_balance : ofReal ∘ balance f = balance (ofReal ∘ f : ι → 𝕜) := by
  simp [balance]

end RCLike
