import Mathlib.Analysis.NormedSpace.OperatorNorm.Mul

namespace ContinuousLinearMap
variable {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [NonUnitalSeminormedCommRing R] [NormedSpace 𝕜 R]
  [IsScalarTower 𝕜 R R] [SMulCommClass 𝕜 R R]

@[simp] lemma flip_mul : (ContinuousLinearMap.mul 𝕜 R).flip = .mul 𝕜 R := by ext; simp [mul_comm]

end ContinuousLinearMap
