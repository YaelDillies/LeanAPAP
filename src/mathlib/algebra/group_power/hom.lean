import mathlib.algebra.hom.group_instances
import mathlib.group_theory.order_of_element

open finset fintype (card) function
open_locale big_operators

variables {α β : Type*}

section add_comm_monoid
variables [add_comm_monoid α] [add_comm_monoid β] {n : ℕ}

def nsmul_hom : ℕ →*₀ add_monoid.End α :=
{ to_fun := λ z,
  { to_fun := λ a, z • a,
    map_zero' := nsmul_zero _,
    map_add' := λ x y, nsmul_add _ _ _ },
  map_zero' := by ext; simp,
  map_one' := by ext; simp only [one_nsmul, add_monoid_hom.coe_mk, add_monoid.coe_one, id.def],
  map_mul' := λ x y, by { ext a, exact mul_nsmul _ _ _ } }

@[simp] lemma nsmul_hom_apply (n : ℕ) (a : α) : nsmul_hom n a = n • a := rfl

end add_comm_monoid

section comm_monoid
variables [comm_monoid α] [comm_monoid β] {n : ℕ}

def pow_hom : ℕ →* monoid.End α :=
{ to_fun := λ z,
  { to_fun := λ a, a ^ z,
    map_one' := one_pow _,
    map_mul' := λ x y, mul_pow _ _ _ },
  map_one' := by ext; simp only [pow_one, monoid_hom.coe_mk, monoid.coe_one, id.def],
  map_mul' := λ x y, by { ext a, exact pow_mul' _ _ _ } }

@[simp] lemma pow_hom_apply (n : ℕ) (a : α) : pow_hom n a = a ^ n := rfl

end comm_monoid

section add_comm_group
variables [add_comm_group α] [fintype α] {a : α} {n : ℕ}

@[simp] lemma nsmul_hom_card : (nsmul_hom (card α) : add_monoid.End α) = 0 :=
by ext; exact card_nsmul_eq_zero

@[simp] lemma nsmul_hom_mod (n : ℕ) : (nsmul_hom (n % card α) : add_monoid.End α) = nsmul_hom n :=
by ext; simp

end add_comm_group

section comm_group
variables [comm_group α] [fintype α] {a : α} {n : ℕ}

lemma pow_hom_card (a : α) : pow_hom (card α) a = 1 := pow_card_eq_one

@[simp] lemma pow_hom_mod_card (n : ℕ) : (pow_hom (n % card α) : monoid.End α) = pow_hom n :=
by ext; simp

end comm_group
