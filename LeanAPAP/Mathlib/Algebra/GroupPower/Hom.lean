import LeanAPAP.Mathlib.Algebra.Hom.GroupInstances
import LeanAPAP.Mathlib.GroupTheory.OrderOfElement

#align_import mathlib.algebra.group_power.hom

open Finset

open Fintype (card)

open Function

open scoped BigOperators

variable {α β : Type*}

section AddCommMonoid
variable [AddCommMonoid α] [AddCommMonoid β] {n : ℕ}

def nsmulHom : ℕ →*₀ AddMonoid.End α
    where
  toλ z :=
    { toλ := λ a => z • a
      map_zero' := nsmul_zero _
      map_add' := λ x y => nsmul_add _ _ _ }
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp only [one_nsmul, AddMonoidHom.coe_mk, AddMonoid.coe_one, id.def]
  map_mul' x y := by ext a; exact mul_nsmul' _ _ _

@[simp]
lemma nsmulHom_apply (n : ℕ) (a : α) : nsmulHom n a = n • a := rfl

end AddCommMonoid

section CommMonoid
variable [CommMonoid α] [CommMonoid β] {n : ℕ}

def powHom : ℕ →* Monoid.End α
    where
  toλ z :=
    { toλ := λ a => a ^ z
      map_one' := one_pow _
      map_mul' := λ x y => mul_pow _ _ _ }
  map_one' := by ext <;> simp only [pow_one, MonoidHom.coe_mk, Monoid.coe_one, id.def]
  map_mul' x y := by ext a; exact pow_mul' _ _ _

@[simp]
lemma powHom_apply (n : ℕ) (a : α) : powHom n a = a ^ n := rfl

end CommMonoid

section AddCommGroup
variable [AddCommGroup α] [Fintype α] {a : α} {n : ℕ}

@[simp]
lemma nsmulHom_card : (nsmulHom (card α) : AddMonoid.End α) = 0 := by
  ext <;> exact card_nsmul_eq_zero

@[simp]
lemma nsmulHom_mod (n : ℕ) : (nsmulHom (n % card α) : AddMonoid.End α) = nsmulHom n := by
  ext <;> simp

end AddCommGroup

section CommGroup
variable [CommGroup α] [Fintype α] {a : α} {n : ℕ}

lemma powHom_card (a : α) : powHom (card α) a = 1 :=
  pow_card_eq_one

@[simp]
lemma powHom_mod_card (n : ℕ) : (powHom (n % card α) : Monoid.End α) = powHom n := by ext <;> simp

end CommGroup
