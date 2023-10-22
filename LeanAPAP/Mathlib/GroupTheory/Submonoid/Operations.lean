import Mathlib.Algebra.Parity
import Mathlib.Algebra.GroupWithZero.Power
import Mathlib.Data.Rat.Order
import Mathlib.GroupTheory.Submonoid.Operations
import LeanAPAP.Mathlib.Data.Rat.Order
import LeanAPAP.Mathlib.GroupTheory.Submonoid.Basic

namespace Submonoid
variable {M : Type*} [MulOneClass M] {S : Submonoid M}

@[to_additive (attr := simp)]
lemma mk_eq_one {a : M} {ha} : (⟨a, ha⟩ : S) = 1 ↔ a = 1 := by simp [←SetLike.coe_eq_coe]

end Submonoid

open AddSubmonoid Set

namespace Nat

@[simp] lemma addSubmonoid_closure_one : closure ({1} : Set ℕ) = ⊤ := by
  refine' (eq_top_iff' _).2 (Nat.rec _ _)
  · exact zero_mem _
  · simp_rw [Nat.succ_eq_add_one]
    exact fun n hn ↦ AddSubmonoid.add_mem _ hn (subset_closure $ Set.mem_singleton _)

end Nat

namespace Rat

@[simp] lemma addSubmonoid_closure_range_pow {n : ℕ} (hn₀ : n ≠ 0) (hn : Even n) :
    closure (range fun x : ℚ ↦ x ^ n) = nonneg _ := by
  refine' le_antisymm (closure_le.2 $ range_subset_iff.2 hn.pow_nonneg) fun x hx ↦ _
  suffices x = (x.num.natAbs * x.den ^ (n - 1)) • (x.den : ℚ)⁻¹ ^ n by
    rw [this]
    exact nsmul_mem (subset_closure $ mem_range_self _) _
  rw [nsmul_eq_mul]
  push_cast
  rw [mul_assoc, pow_sub₀, pow_one, mul_right_comm, ←mul_pow, mul_inv_cancel, one_pow, one_mul, ←
    Int.cast_ofNat, Int.coe_natAbs, abs_of_nonneg, ←div_eq_mul_inv, num_div_den]
  rw [mem_zeroLe] at hx
  any_goals positivity
  exact pos_iff_ne_zero.2 hn₀

@[simp]
lemma addSubmonoid_closure_range_mul_self : closure (range fun x : ℚ ↦ x * x) = nonneg _ := by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero even_two

end Rat
