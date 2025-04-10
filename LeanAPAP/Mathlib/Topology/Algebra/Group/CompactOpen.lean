import LeanAPAP.Mathlib.Topology.CompactOpen
import Mathlib.Topology.Algebra.Group.CompactOpen

open Topology

namespace ContinuousMonoidHom
variable {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
  [DiscreteTopology M] [ContinuousMul N] [T2Space N]

@[to_additive]
lemma isClosedEmbedding_coe : IsClosedEmbedding ((⇑) : (M →ₜ* N) → M → N) :=
  ContinuousMap.isHomeomorph_coe.isClosedEmbedding.comp <| isClosedEmbedding_toContinuousMap ..

@[to_additive]
instance [CompactSpace N] : CompactSpace (M →ₜ* N) :=
  ContinuousMonoidHom.isClosedEmbedding_coe.compactSpace

end ContinuousMonoidHom
