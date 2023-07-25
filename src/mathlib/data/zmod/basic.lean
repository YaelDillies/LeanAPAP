import data.zmod.basic
import mathlib.group_theory.order_of_element

open fintype function

namespace zmod
variables {m n : ℕ} {x y : zmod n}

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

lemma val_one'' : ∀ {n}, n ≠ 1 → (1 : zmod n).val = 1
| 0 _ := rfl
| 1 hn := by cases hn rfl
| (n + 2) _ := by haveI : fact (1 < n + 2) := ⟨by simp⟩; exact zmod.val_one _

@[simp] protected lemma inv_one (n : ℕ) : (1⁻¹ : zmod n) = 1 :=
begin
  obtain rfl | hn := eq_or_ne n 1,
  { exact subsingleton.elim _ _ },
  { simpa [zmod.val_one'' hn] using mul_inv_eq_gcd (1 : zmod n) }
end

lemma mul_val_inv (hmn : m.coprime n) : (m * (m⁻¹ : zmod n).val : zmod n) = 1 :=
begin
  obtain rfl | hn := eq_or_ne n 0,
  { simp [m.coprime_zero_right.1 hmn] },
  haveI : ne_zero n := ⟨hn⟩,
  rw [zmod.nat_cast_zmod_val, zmod.coe_mul_inv_eq_one _ hmn],
end

lemma val_inv_mul (hmn : m.coprime n) : ((m⁻¹ : zmod n).val * m : zmod n) = 1 :=
by rw [mul_comm, mul_val_inv hmn]

variables {A : Type*} [add_comm_group A]

lemma lift_injective {f : {f : ℤ →+ A // f n = 0}} :
  injective (lift n f) ↔ ∀ i : ℤ, f i = 0 → (i : zmod n) = 0 :=
by simp only [←add_monoid_hom.ker_eq_bot_iff, eq_bot_iff, set_like.le_def,
  zmod.int_cast_surjective.forall, zmod.lift_coe, add_monoid_hom.mem_ker, add_subgroup.mem_bot]

end zmod


section group
variables {α : Type*} [group α] [fintype α] {n : ℕ}

--TODO: Fix additivisation
@[simp] lemma pow_zmod_val_inv_pow (hn : n.coprime (card α)) (a : α) :
  (a ^ (n⁻¹ : zmod (card α)).val) ^ n = a :=
by rw [←pow_mul', ←pow_mod_card, ←zmod.val_nat_cast, nat.cast_mul, zmod.mul_val_inv hn,
  zmod.val_one_eq_one_mod, pow_mod_card, pow_one]

@[simp] lemma pow_pow_zmod_val_inv (hn : n.coprime (card α)) (a : α) :
  (a ^ n) ^ (n⁻¹ : zmod (card α)).val = a :=
by rw [pow_right_comm, pow_zmod_val_inv_pow hn]

lemma pow_bijective (hn : n.coprime (card α)) : bijective ((^ n) : α → α) :=
bijective_iff_has_inverse.2
  ⟨(^ (n⁻¹ : zmod (card α)).val), pow_pow_zmod_val_inv hn, pow_zmod_val_inv_pow hn⟩

end group

section add_group
variables {α : Type*} [add_group α] [fintype α] {n : ℕ}

--TODO: Additivise
@[simp] lemma nsmul_zmod_val_inv_nsmul (hn : n.coprime (card α)) (a : α) :
  n • (n⁻¹ : zmod (card α)).val • a = a :=
by rw [←mul_nsmul, ←mod_card_nsmul, ←zmod.val_nat_cast, nat.cast_mul, zmod.mul_val_inv hn,
  zmod.val_one_eq_one_mod, mod_card_nsmul, one_nsmul]

@[simp] lemma zmod_val_inv_nsmul_nsmul (hn : n.coprime (card α)) (a : α) :
  (n⁻¹ : zmod (card α)).val • n • a = a :=
by rw [nsmul_left_comm, nsmul_zmod_val_inv_nsmul hn]

lemma nsmul_bijective (hn : n.coprime (card α)) : bijective ((•) n : α → α) :=
bijective_iff_has_inverse.2
  ⟨(•) (n⁻¹ : zmod (card α)).val, zmod_val_inv_nsmul_nsmul hn, nsmul_zmod_val_inv_nsmul hn⟩

attribute [to_additive nsmul_zmod_val_inv_nsmul] pow_zmod_val_inv_pow
attribute [to_additive zmod_val_inv_nsmul_nsmul] pow_pow_zmod_val_inv
attribute [to_additive] pow_bijective

end add_group
