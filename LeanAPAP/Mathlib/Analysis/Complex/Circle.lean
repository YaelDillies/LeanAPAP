import Mathlib.Analysis.Complex.Circle

/-!
## TODO

Rename
* `expMapCircle` → `circle.exp`
* `coe_inv_circle_eq_conj` → `circle.coe_inv_eq_conj`
* `coe_div_circle` → `circle.coe_div` + `norm_cast`
-/

attribute [norm_cast] coe_div_circle

open Multiplicative Real
open scoped ComplexConjugate Real

namespace Circle

@[simp, norm_cast] lemma coe_exp (r : ℝ) : ↑(expMapCircle r) = Complex.exp (r * Complex.I) := rfl

end Circle
