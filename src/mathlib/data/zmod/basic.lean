import data.zmod.basic

namespace zmod
variables {n : ℕ} {x y : zmod n}

lemma coe_add : ((x + y : zmod n) : ℤ) = (x + y) % n :=
by rw [←zmod.coe_int_cast, int.cast_add, zmod.int_cast_zmod_cast, zmod.int_cast_zmod_cast]

lemma coe_mul : ((x * y : zmod n) : ℤ) = (x * y) % n :=
by rw [←zmod.coe_int_cast, int.cast_mul, zmod.int_cast_zmod_cast, zmod.int_cast_zmod_cast]

lemma coe_sub : ((x - y : zmod n) : ℤ) = (x - y) % n :=
by rw [←zmod.coe_int_cast, int.cast_sub, zmod.int_cast_zmod_cast, zmod.int_cast_zmod_cast]

lemma coe_neg : ((- x : zmod n) : ℤ) = (- x) % n :=
by rw [←zmod.coe_int_cast, int.cast_neg, zmod.int_cast_zmod_cast]

lemma subsingleton_of_eq_one : ∀ {n : ℕ} (x y : zmod n), n = 1 → x = y
| _ _ _ rfl := subsingleton.elim _ _

end zmod
