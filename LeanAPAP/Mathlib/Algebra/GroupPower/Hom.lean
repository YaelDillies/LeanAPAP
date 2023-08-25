import Project.Mathlib.Algebra.Hom.GroupInstances
import Project.Mathlib.GroupTheory.OrderOfElement

#align_import mathlib.algebra.group_power.hom

open Finset

open Fintype (card)

open Function

open scoped BigOperators

variable {α β : Type _}

section AddCommMonoid

variable [AddCommMonoid α] [AddCommMonoid β] {n : ℕ}

def nsmulHom : ℕ →*₀ AddMonoid.End α
    where
  toFun z :=
    { toFun := fun a => z • a
      map_zero' := nsmul_zero _
      map_add' := fun x y => nsmul_add _ _ _ }
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp only [one_nsmul, AddMonoidHom.coe_mk, AddMonoid.coe_one, id.def]
  map_mul' x y := by ext a; exact mul_nsmul' _ _ _

@[simp]
theorem nsmulHom_apply (n : ℕ) (a : α) : nsmulHom n a = n • a :=
  rfl

end AddCommMonoid

section CommMonoid

variable [CommMonoid α] [CommMonoid β] {n : ℕ}

def powHom : ℕ →* Monoid.End α
    where
  toFun z :=
    { toFun := fun a => a ^ z
      map_one' := one_pow _
      map_mul' := fun x y => mul_pow _ _ _ }
  map_one' := by ext <;> simp only [pow_one, MonoidHom.coe_mk, Monoid.coe_one, id.def]
  map_mul' x y := by ext a; exact pow_mul' _ _ _

@[simp]
theorem powHom_apply (n : ℕ) (a : α) : powHom n a = a ^ n :=
  rfl

end CommMonoid

section AddCommGroup

variable [AddCommGroup α] [Fintype α] {a : α} {n : ℕ}

@[simp]
theorem nsmulHom_card : (nsmulHom (card α) : AddMonoid.End α) = 0 := by
  ext <;> exact card_nsmul_eq_zero

@[simp]
theorem nsmulHom_mod (n : ℕ) : (nsmulHom (n % card α) : AddMonoid.End α) = nsmulHom n := by
  ext <;> simp

end AddCommGroup

section CommGroup

variable [CommGroup α] [Fintype α] {a : α} {n : ℕ}

theorem powHom_card (a : α) : powHom (card α) a = 1 :=
  pow_card_eq_one

@[simp]
theorem powHom_mod_card (n : ℕ) : (powHom (n % card α) : Monoid.End α) = powHom n := by ext <;> simp

end CommGroup

