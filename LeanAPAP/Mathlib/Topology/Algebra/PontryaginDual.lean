import LeanAPAP.Mathlib.Topology.Algebra.Group.CompactOpen
import Mathlib.Topology.Algebra.PontryaginDual

namespace PontryaginDual
variable {M : Type*} [Monoid M] [TopologicalSpace M]

/-- A discrete monoid has compact Pontryagin dual. -/
instance [DiscreteTopology M] : CompactSpace (PontryaginDual M) :=
  ContinuousMonoidHom.isClosedEmbedding_coe.compactSpace

/-- A compact monoid has discrete Pontryagin dual. -/
instance [CompactSpace M] : DiscreteTopology (PontryaginDual M) := sorry

instance [DiscreteTopology M] [CompactSpace M] : Finite (PontryaginDual M) :=
  finite_of_compact_of_discrete

noncomputable instance [DiscreteTopology M] [CompactSpace M] : Fintype (PontryaginDual M) :=
  .ofFinite _

end PontryaginDual
