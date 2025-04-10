import Mathlib.Algebra.Group.Translate
import Mathlib.Analysis.Convolution

/-!
# TODO

Extra arguments to `convolution_zero`
-/

open ContinuousLinearMap Function
open scoped Convolution translate

namespace MeasureTheory
variable {𝕜 G E E' F F' F'' E'' : Type*}

section NontriviallyNormedField
variable [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup E'']
  [NormedAddCommGroup F] [NormedAddCommGroup F'] [NormedAddCommGroup F'']
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 E'']
  [NormedSpace 𝕜 F] [NormedSpace 𝕜 F'] [NormedSpace 𝕜 F'']
  {f : G → E} {g g' : G → E'} {L : E →L[𝕜] E' →L[𝕜] F}
  [MeasurableSpace G] {μ ν : Measure G} [AddGroup G]

lemma ConvolutionExists.of_finite [Finite G] [MeasurableSingletonClass G] [IsFiniteMeasure μ] :
    ConvolutionExists f g L μ := fun _ ↦ .of_finite

end NontriviallyNormedField

section RCLike
variable [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup E'']
  [NormedAddCommGroup F]
variable [NormedSpace 𝕜 E]
variable [NormedSpace 𝕜 E']
variable [NormedSpace 𝕜 E'']
variable [NormedSpace ℝ F] [NormedSpace 𝕜 F]
variable {n : ℕ∞}
variable [MeasurableSpace G] {μ ν : Measure G}
variable (L : E →L[𝕜] E' →L[𝕜] F)

section Assoc
variable [CompleteSpace F]
variable [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [CompleteSpace F']
variable [NormedAddCommGroup F''] [NormedSpace ℝ F''] [NormedSpace 𝕜 F''] [CompleteSpace F'']
variable {k : G → E''}
variable (L₂ : F →L[𝕜] E'' →L[𝕜] F')
variable (L₃ : E →L[𝕜] F'' →L[𝕜] F')
variable (L₄ : E' →L[𝕜] E'' →L[𝕜] F'')
variable [AddGroup G]
variable [SFinite μ] [SFinite ν] [μ.IsAddRightInvariant] {f g}

variable [MeasurableAdd₂ G] [ν.IsAddRightInvariant] [MeasurableNeg G]

/-- Convolution is associative. This has a weak but inconvenient integrability condition.
See also `MeasureTheory.convolution_assoc`. -/
-- TODO: Rename `convolution_assoc'` to `convolution_assoc_apply'`
theorem convolution_assoc''' (hL : ∀ x y z, L₂ (L x y) z = L₃ x (L₄ y z))
    (hfg : ∀ᵐ y ∂μ, ConvolutionExistsAt f g y L ν)
    (hgk : ∀ᵐ x ∂ν, ConvolutionExistsAt g k x L₄ μ)
    (hi : ∀ x₀,
      Integrable (uncurry fun x y => (L₃ (f y)) ((L₄ (g (x - y))) (k (x₀ - x)))) (μ.prod ν)) :
    (f ⋆[L, ν] g) ⋆[L₂, μ] k = f ⋆[L₃, ν] (g ⋆[L₄, μ] k) :=
  funext fun _ ↦ convolution_assoc' _ _ _ _ hL hfg hgk (hi _)

/-- Convolution is associative. This requires that
* all maps are a.e. strongly measurable w.r.t one of the measures
* `f ⋆[L, ν] g` exists almost everywhere
* `‖g‖ ⋆[μ] ‖k‖` exists almost everywhere
* `‖f‖ ⋆[ν] (‖g‖ ⋆[μ] ‖k‖)` exists at `x₀` -/
-- TODO: Rename `convolution_assoc` to `convolution_assoc_apply`
theorem convolution_assoc'' (hL : ∀ x y z, L₂ (L x y) z = L₃ x (L₄ y z))
    (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g μ) (hk : AEStronglyMeasurable k μ)
    (hfg : ∀ᵐ y ∂μ, ConvolutionExistsAt f g y L ν)
    (hgk : ∀ᵐ x ∂ν, ConvolutionExistsAt (‖g ·‖) (‖k ·‖) x (mul ℝ ℝ) μ)
    (hfgk : ConvolutionExists (‖f ·‖) ((‖g ·‖) ⋆[mul ℝ ℝ, μ] (‖k ·‖)) (mul ℝ ℝ) ν) :
    (f ⋆[L, ν] g) ⋆[L₂, μ] k = f ⋆[L₃, ν] (g ⋆[L₄, μ] k) :=
  funext fun _ ↦ convolution_assoc _ _ _ _ hL hf hg hk hfg hgk (hfgk _)

end Assoc

section reindex
variable [AddCommGroup G] {f : G → E} {g : G → E'} {a : G}

/-- This is the definition. -/
lemma convolution_eq_integral_sub (a : G) (f : G → E) (g : G → E') :
    (f ⋆[L, ν] g) a = ∫ t, L (f t) (g (a - t)) ∂ν := rfl

lemma convolution_eq_integral_neg_add [MeasurableNeg G] [ν.IsNegInvariant] (f : G → E) (g : G → E')
    (a : G) : (f ⋆[L, ν] g) a = ∫ t, L (f (-t)) (g (a + t)) ∂ν := by
  rw [convolution_eq_integral_sub, ← integral_neg_eq_self]; simp

variable [MeasurableAdd G] [ν.IsAddLeftInvariant]

lemma convolution_eq_integral_add_neg (f : G → E) (g : G → E') (a : G) :
    (f ⋆[L, ν] g) a = ∫ t, L (f (a + t)) (g (-t)) ∂ν := by
  rw [convolution_eq_integral_sub, ← integral_add_left_eq_self _ a]; simp

lemma convolution_apply_add (f : G → E) (g : G → E') (a b : G) :
    (f ⋆[L, ν] g) (a + b) = ∫ t, L (f (a + t)) (g (b - t)) ∂ν := by
  rw [convolution_eq_integral_sub, ← integral_add_left_eq_self _ a]; simp

lemma convolution_eq_integral_sub' [MeasurableNeg G] [ν.IsNegInvariant] (f : G → E) (g : G → E')
    (a : G) : (f ⋆[L, ν] g) a = ∫ t, L (f (a - t)) (g t) ∂ν := by
  rw [convolution_eq_integral_sub, ← integral_sub_left_eq_self _ _ a]; simp

end reindex

section translate
variable [AddCommGroup G] {f : G → E} {g : G → E'} {a : G}

@[simp] lemma convolution_translate (f : G → E) (g : G → E') (a : G) :
    f ⋆[L, ν] τ a g = τ a (f ⋆[L, ν] g) := by
  ext b; simp [convolution, sub_right_comm]

variable [MeasurableAdd G] [ν.IsAddLeftInvariant]

@[simp] lemma translate_convolution (f : G → E) (g : G → E') (a : G) :
    τ a f ⋆[L, ν] g = τ a (f ⋆[L, ν] g) := by
  ext b; simpa using integral_sub_right_eq_self (fun t ↦ L (f t) (g (b - a - t))) a

end translate
end RCLike
end MeasureTheory
