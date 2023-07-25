import algebra.parity
import algebra.group_with_zero.power
import data.rat.order
import group_theory.submonoid.operations
import mathlib.data.rat.order
import mathlib.group_theory.submonoid.basic

namespace submonoid
variables {M : Type*} [mul_one_class M] {S : submonoid M}

@[simp, to_additive] lemma mk_eq_one {a : M} {ha} : (⟨a, ha⟩ : S) = 1 ↔ a = 1 :=
by simp [←set_like.coe_eq_coe]

end submonoid

open add_submonoid set

namespace nat

@[simp] lemma add_submonoid_closure_one : closure ({1} : set ℕ) = ⊤ :=
begin
  refine (eq_top_iff' _).2 (nat.rec _ _),
  { exact zero_mem _ },
  { simp_rw nat.succ_eq_add_one,
    exact λ n hn, add_submonoid.add_mem _ hn (subset_closure $ set.mem_singleton _) }
end

end nat

namespace rat

@[simp] lemma add_submonoid_closure_range_pow {n : ℕ} (hn₀ : n ≠ 0) (hn : even n) :
  closure (range $ λ x : ℚ, x ^ n) = nonneg _ :=
begin
  refine le_antisymm (closure_le.2 $ range_subset_iff.2 hn.pow_nonneg) (λ x hx, _),
  suffices : x = (x.num.nat_abs * x.denom ^ (n - 1)) • x.denom⁻¹ ^ n,
  { rw this,
    exact nsmul_mem (subset_closure $ mem_range_self _) _ },
  rw [nsmul_eq_mul],
  push_cast,
  rw [mul_assoc, pow_sub₀, pow_one, mul_right_comm, ←mul_pow, mul_inv_cancel, one_pow, one_mul,
    ←int.cast_coe_nat, int.coe_nat_abs, abs_of_nonneg, ←div_eq_mul_inv, num_div_denom],
    dsimp at hx,
  any_goals { positivity },
  exact pos_iff_ne_zero.2 hn₀,
end

@[simp] lemma add_submonoid_closure_range_mul_self : closure (range $ λ x : ℚ, x * x) = nonneg _ :=
by simpa only [sq] using add_submonoid_closure_range_pow two_ne_zero even_two

end rat
