import Mathlib.Analysis.Convolution

/-!
# TODO

Extra arguments to `convolution_zero`
-/

namespace MeasureTheory
variable {𝕜 G E E' F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup F]
  {f : G → E} {g g' : G → E'} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 E']
  [NormedSpace 𝕜 F] {L : E →L[𝕜] E' →L[𝕜] F} [MeasurableSpace G] {μ : Measure G} [AddGroup G]

lemma ConvolutionExists.of_finite [Finite G] [MeasurableSingletonClass G] [IsFiniteMeasure μ] :
    ConvolutionExists f g L μ := fun _ ↦ .of_finite

end MeasureTheory
