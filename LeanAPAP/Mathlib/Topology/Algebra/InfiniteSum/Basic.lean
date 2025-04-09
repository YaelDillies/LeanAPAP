import Mathlib.Topology.Algebra.InfiniteSum.Basic

variable {ι κ M : Type*} [CommMonoid M] [TopologicalSpace M]

@[to_additive]
lemma tprod_equiv (e : ι ≃ κ) (f : ι → M) (g : κ → M) (h : ∀ x, f x = g (e x)) :
    ∏' x, f x = ∏' x, g x := by simpa [h] using e.tprod_eq g
