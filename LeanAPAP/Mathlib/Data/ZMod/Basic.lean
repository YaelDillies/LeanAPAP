import Mathlib.Data.ZMod.Basic
import LeanAPAP.Mathlib.Data.FunLike.Basic
import LeanAPAP.Mathlib.GroupTheory.OrderOfElement

open Fintype Function

namespace ZMod
variable {m n : ℕ}

section
variable {x y : ZMod n}

lemma coe_add : ((x + y : ZMod n) : ℤ) = (x + y) % n := by
  rw [← ZMod.coe_int_cast, Int.cast_add, ZMod.int_cast_zmod_cast, ZMod.int_cast_zmod_cast]

lemma coe_mul : ((x * y : ZMod n) : ℤ) = x * y % n := by
  rw [← ZMod.coe_int_cast, Int.cast_mul, ZMod.int_cast_zmod_cast, ZMod.int_cast_zmod_cast]

lemma coe_sub : ((x - y : ZMod n) : ℤ) = (x - y) % n := by
  rw [← ZMod.coe_int_cast, Int.cast_sub, ZMod.int_cast_zmod_cast, ZMod.int_cast_zmod_cast]

lemma coe_neg : ((-x : ZMod n) : ℤ) = -x % n := by
  rw [← ZMod.coe_int_cast, Int.cast_neg, ZMod.int_cast_zmod_cast]

end

lemma subsingleton_of_eq_one : ∀ {n : ℕ} (x y : ZMod n), n = 1 → x = y
  | _, _, _, rfl => Subsingleton.elim _ _

lemma val_one'' : ∀ {n}, n ≠ 1 → (1 : ZMod n).val = 1
  | 0, _ => rfl
  | 1, hn => by cases hn rfl
  | n + 2, _ =>
    haveI : Fact (1 < n + 2) := ⟨by simp⟩
    ZMod.val_one _

@[simp] protected lemma inv_one (n : ℕ) : (1⁻¹ : ZMod n) = 1 := by
  obtain rfl | hn := eq_or_ne n 1
  · exact Subsingleton.elim _ _
  · simpa [ZMod.val_one'' hn] using mul_inv_eq_gcd (1 : ZMod n)

lemma mul_val_inv (hmn : m.Coprime n) : (m * (m⁻¹ : ZMod n).val : ZMod n) = 1 := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [m.coprime_zero_right.1 hmn]
  haveI : NeZero n := ⟨hn⟩
  rw [ZMod.nat_cast_zmod_val, ZMod.coe_mul_inv_eq_one _ hmn]

lemma val_inv_mul (hmn : m.Coprime n) : ((m⁻¹ : ZMod n).val * m : ZMod n) = 1 := by
  rw [mul_comm, mul_val_inv hmn]

variable {A : Type*} [AddCommGroup A]

lemma lift_injective {f : {f : ℤ →+ A // f n = 0}} :
    Injective (lift n f) ↔ ∀ i : ℤ, f i = 0 → (i : ZMod n) = 0 := by
  simp only [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff, SetLike.le_def, Subtype.coe_coe,
    ZMod.int_cast_surjective.forall, ZMod.lift_coe, AddMonoidHom.mem_ker, AddSubgroup.mem_bot]

end ZMod

section Group
variable {α : Type*} [Group α] {n : ℕ}

--TODO: Fix additivisation
lemma pow_zmod_val_inv_pow (hn : (Nat.card α).Coprime n) (a : α) :
    (a ^ (n⁻¹ : ZMod (Nat.card α)).val) ^ n = a := by
  rw [← pow_mul', ← pow_mod_natCard, ← ZMod.val_nat_cast, Nat.cast_mul, ZMod.mul_val_inv hn.symm,
    ZMod.val_one_eq_one_mod, pow_mod_natCard, pow_one]

lemma pow_pow_zmod_val_inv (hn : (Nat.card α).Coprime n) (a : α) :
    (a ^ n) ^ (n⁻¹ : ZMod (Nat.card α)).val = a := by rw [pow_right_comm, pow_zmod_val_inv_pow hn]

end Group

section AddGroup
variable {α : Type*} [AddGroup α] {n : ℕ}

--TODO: Additivise
@[simp]
lemma nsmul_zmod_val_inv_nsmul (hn : (Nat.card α).Coprime n) (a : α) :
    n • (n⁻¹ : ZMod (Nat.card α)).val • a = a := by
  rw [← mul_nsmul', ← mod_natCard_nsmul, ← ZMod.val_nat_cast, Nat.cast_mul,
    ZMod.mul_val_inv hn.symm, ZMod.val_one_eq_one_mod, mod_natCard_nsmul, one_nsmul]

@[simp]
lemma zmod_val_inv_nsmul_nsmul (hn : (Nat.card α).Coprime n) (a : α) :
    (n⁻¹ : ZMod (Nat.card α)).val • n • a = a := by
  rw [nsmul_left_comm, nsmul_zmod_val_inv_nsmul hn]

attribute [to_additive (attr := simp) existing nsmul_zmod_val_inv_nsmul] pow_zmod_val_inv_pow
attribute [to_additive (attr := simp) existing zmod_val_inv_nsmul_nsmul] pow_pow_zmod_val_inv

end AddGroup
