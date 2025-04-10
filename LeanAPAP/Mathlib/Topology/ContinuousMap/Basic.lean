import Mathlib.Topology.ContinuousMap.Basic

namespace ContinuousMap
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [DiscreteTopology X]

@[simp] lemma coe_equivFnOfDiscrete (f : C(X, Y)) : equivFnOfDiscrete X Y f = f := rfl
@[simp] lemma coe_equivFnOfDiscrete_symm (f : X → Y) : (equivFnOfDiscrete X Y).symm f = f := rfl

end ContinuousMap
