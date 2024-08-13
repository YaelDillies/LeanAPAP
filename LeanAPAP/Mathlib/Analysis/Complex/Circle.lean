import Mathlib.Analysis.Complex.Circle

open Function

namespace Circle
variable {x y : Circle}

@[simp, norm_cast] lemma coe_exp (r : ℝ) : ↑(exp r) = Complex.exp (r * Complex.I) := rfl

@[ext] lemma ext : (x : ℂ) = y → x = y := Subtype.ext

lemma coe_injective : Injective ((↑) : Circle → ℂ) := fun _ _ ↦ ext

@[simp] lemma coe_inj : (x : ℂ) = y ↔ x = y := coe_injective.eq_iff
@[simp] lemma coe_eq_one : (x : ℂ) = 1 ↔ x = 1 := by rw [← coe_inj, coe_one]

end Circle
