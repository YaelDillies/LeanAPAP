import Mathlib.Analysis.Calculus.Deriv.Basic

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f f' : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}

lemma deriv_eqOn (hs : IsOpen s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) :
    s.EqOn (deriv f) f' := fun x hx ↦ by
  rw [← derivWithin_of_isOpen hs hx, (hf' _ hx).derivWithin $ hs.uniqueDiffWithinAt hx]
