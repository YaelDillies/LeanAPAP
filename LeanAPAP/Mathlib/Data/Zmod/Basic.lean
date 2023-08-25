import Mathbin.Data.Zmod.Basic
import Project.Mathlib.GroupTheory.OrderOfElement

#align_import mathlib.data.zmod.basic

open Fintype Function

namespace ZMod

variable {m n : ℕ} {x y : ZMod n}

theorem coe_add : ((x + y : ZMod n) : ℤ) = (x + y) % n := by
  rw [← ZMod.coe_int_cast, Int.cast_add, ZMod.int_cast_zmod_cast, ZMod.int_cast_zmod_cast]

theorem coe_hMul : ((x * y : ZMod n) : ℤ) = x * y % n := by
  rw [← ZMod.coe_int_cast, Int.cast_mul, ZMod.int_cast_zmod_cast, ZMod.int_cast_zmod_cast]

theorem coe_sub : ((x - y : ZMod n) : ℤ) = (x - y) % n := by
  rw [← ZMod.coe_int_cast, Int.cast_sub, ZMod.int_cast_zmod_cast, ZMod.int_cast_zmod_cast]

theorem coe_neg : ((-x : ZMod n) : ℤ) = -x % n := by
  rw [← ZMod.coe_int_cast, Int.cast_neg, ZMod.int_cast_zmod_cast]

theorem subsingleton_of_eq_one : ∀ {n : ℕ} (x y : ZMod n), n = 1 → x = y
  | _, _, _, rfl => Subsingleton.elim _ _

theorem val_one'' : ∀ {n}, n ≠ 1 → (1 : ZMod n).val = 1
  | 0, _ => rfl
  | 1, hn => by cases hn rfl
  | n + 2, _ =>
    haveI : Fact (1 < n + 2) := ⟨by simp⟩
    ZMod.val_one _

@[simp]
protected theorem inv_one (n : ℕ) : (1⁻¹ : ZMod n) = 1 :=
  by
  obtain rfl | hn := eq_or_ne n 1
  · exact Subsingleton.elim _ _
  · simpa [ZMod.val_one'' hn] using mul_inv_eq_gcd (1 : ZMod n)

theorem hMul_val_inv (hmn : m.coprime n) : (m * (m⁻¹ : ZMod n).val : ZMod n) = 1 :=
  by
  obtain rfl | hn := eq_or_ne n 0
  · simp [m.coprime_zero_right.1 hmn]
  haveI : NeZero n := ⟨hn⟩
  rw [ZMod.nat_cast_zmod_val, ZMod.coe_mul_inv_eq_one _ hmn]

theorem val_inv_hMul (hmn : m.coprime n) : ((m⁻¹ : ZMod n).val * m : ZMod n) = 1 := by
  rw [mul_comm, mul_val_inv hmn]

variable {A : Type _} [AddCommGroup A]

theorem lift_injective {f : { f : ℤ →+ A // f n = 0 }} :
    Injective (lift n f) ↔ ∀ i : ℤ, f i = 0 → (i : ZMod n) = 0 := by
  simp only [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff, SetLike.le_def,
    zmod.int_cast_surjective.forall, ZMod.lift_coe, AddMonoidHom.mem_ker, AddSubgroup.mem_bot]

end ZMod

section Group

variable {α : Type _} [Group α] [Fintype α] {n : ℕ}

--TODO: Fix additivisation
@[simp]
theorem pow_zMod_val_inv_pow (hn : n.coprime (card α)) (a : α) :
    (a ^ (n⁻¹ : ZMod (card α)).val) ^ n = a := by
  rw [← pow_mul', ← pow_mod_card, ← ZMod.val_nat_cast, Nat.cast_mul, ZMod.hMul_val_inv hn,
    ZMod.val_one_eq_one_mod, pow_mod_card, pow_one]

@[simp]
theorem pow_pow_zMod_val_inv (hn : n.coprime (card α)) (a : α) :
    (a ^ n) ^ (n⁻¹ : ZMod (card α)).val = a := by rw [pow_right_comm, pow_zMod_val_inv_pow hn]

theorem pow_bijective (hn : n.coprime (card α)) : Bijective ((· ^ n) : α → α) :=
  bijective_iff_has_inverse.2
    ⟨(· ^ (n⁻¹ : ZMod (card α)).val), pow_pow_zMod_val_inv hn, pow_zMod_val_inv_pow hn⟩

end Group

section AddGroup

variable {α : Type _} [AddGroup α] [Fintype α] {n : ℕ}

--TODO: Additivise
@[simp]
theorem nsmul_zMod_val_inv_nsmul (hn : n.coprime (card α)) (a : α) :
    n • (n⁻¹ : ZMod (card α)).val • a = a := by
  rw [← mul_nsmul', ← mod_card_nsmul, ← ZMod.val_nat_cast, Nat.cast_mul, ZMod.hMul_val_inv hn,
    ZMod.val_one_eq_one_mod, mod_card_nsmul, one_nsmul]

@[simp]
theorem zMod_val_inv_nsmul_nsmul (hn : n.coprime (card α)) (a : α) :
    (n⁻¹ : ZMod (card α)).val • n • a = a := by rw [nsmul_left_comm, nsmul_zMod_val_inv_nsmul hn]

theorem nsmul_bijective (hn : n.coprime (card α)) : Bijective ((· • ·) n : α → α) :=
  bijective_iff_has_inverse.2
    ⟨(· • ·) (n⁻¹ : ZMod (card α)).val, zMod_val_inv_nsmul_nsmul hn, nsmul_zMod_val_inv_nsmul hn⟩

attribute [to_additive nsmul_zMod_val_inv_nsmul] pow_zMod_val_inv_pow

attribute [to_additive zMod_val_inv_nsmul_nsmul] pow_pow_zMod_val_inv

attribute [to_additive] pow_bijective

end AddGroup

