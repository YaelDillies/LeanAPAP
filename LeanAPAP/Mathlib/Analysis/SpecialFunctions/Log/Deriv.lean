import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Real

attribute [fun_prop] differentiableAt_log DifferentiableAt.log

section fderiv
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E} {f' : E →L[ℝ] ℝ}
  {s : Set E}

@[fun_prop]
protected lemma DifferentiableOn.log (hf : DifferentiableOn ℝ f s) (hs : ∀ x ∈ s, f x ≠ 0) :
    DifferentiableOn ℝ (fun x => log (f x)) s := fun x hx ↦ (hf x hx).log (hs _ hx)

end fderiv
end Real
