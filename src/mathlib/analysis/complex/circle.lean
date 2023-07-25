import analysis.complex.circle
import analysis.special_functions.trigonometric.basic
import mathlib.number_theory.legendre_symbol.add_char.basic

/-!
## TODO

Rename
* `exp_map_circle` → `circle.exp`
* `coe_inv_circle_eq_conj` → `circle.coe_inv_eq_conj`
* `coe_div_circle` → `circle.coe_div` + `norm_cast`
-/

attribute [norm_cast] coe_div_circle

open add_char real
open_locale complex_conjugate real

namespace circle
variables {r : ℝ}

@[simp, norm_cast] lemma coe_exp (r : ℝ) : ↑(exp_map_circle r) = complex.exp (r * complex.I) := rfl

lemma exp_int_mul_two_pi (n : ℤ) : exp_map_circle (n * (2 * π)) = 1 :=
subtype.ext $ by simpa [mul_assoc] using complex.exp_int_mul_two_pi_mul_I n

lemma exp_two_pi_mul_int (n : ℤ) : exp_map_circle (2 * π * n) = 1 :=
by simpa only [mul_comm] using exp_int_mul_two_pi n

lemma exp_two_pi : exp_map_circle (2 * π) = 1 := by simpa using exp_int_mul_two_pi 1

lemma exp_eq_one : exp_map_circle r = 1 ↔ ∃ n : ℤ, r = n * (2 * π) :=
by simp [subtype.ext_iff, complex.exp_eq_one_iff, ←mul_assoc, complex.I_ne_zero,
  ←complex.of_real_inj]

noncomputable def e : add_char ℝ circle :=
add_char.to_monoid_hom'.symm
  { to_fun := λ r, exp_map_circle (2 * π * r.to_add),
    map_one' := by simp,
    map_mul' := by simp [mul_add, complex.exp_add] }

lemma e_apply (r : ℝ) : e r = exp_map_circle (2 * π * r) := rfl

@[simp, norm_cast] lemma coe_e (r : ℝ) : ↑(e r) = complex.exp ((2 * π * r : ℝ) * complex.I) := rfl

@[simp] lemma e_int (z : ℤ) : e z = 1 := exp_two_pi_mul_int _

@[simp] lemma e_one : e 1 = 1 := by simpa using e_int 1

@[simp] lemma e_add_int {z : ℤ} : e (r + z) = e r := by rw [map_add_mul, e_int, mul_one]
@[simp] lemma e_sub_int {z : ℤ} : e (r - z) = e r := by rw [map_sub_eq_div, e_int, div_one]

@[simp] lemma e_fract (r : ℝ) : e (int.fract r) = e r := by rw [int.fract, e_sub_int]

@[simp] lemma e_mod_div {m : ℤ} {n : ℕ} : e ((m % n : ℤ) / n) = e (m / n) :=
begin
  obtain hn | hn := eq_or_ne (n : ℝ) 0,
  { rw [hn, div_zero, div_zero] },
  { rw [int.mod_def, int.cast_sub, sub_div, int.cast_mul, int.cast_coe_nat,
      mul_div_cancel_left _ hn, e_sub_int] }
end

lemma e_eq_one : e r = 1 ↔ ∃ n : ℤ, r = n :=
by simp [e_apply, exp_eq_one, mul_comm (2 * π), pi_ne_zero]

end circle
