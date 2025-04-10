import Mathlib.Topology.CompactOpen

namespace ContinuousMap
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [DiscreteTopology X]

/-- The continuous functions from `X` to `Y` are the same as the plain functions when `X` is
discrete. -/
def homeoFnOfDiscrete : C(X, Y) ≃ₜ (X → Y) where
  __ := equivFnOfDiscrete X Y
  continuous_invFun :=
    continuous_compactOpen.2 fun K hK U hU ↦ isOpen_set_pi hK.finite_of_discrete fun _ _ ↦ hU

lemma isHomeomorph_coe : IsHomeomorph ((⇑) : C(X, Y) → X → Y) := homeoFnOfDiscrete.isHomeomorph

end ContinuousMap
