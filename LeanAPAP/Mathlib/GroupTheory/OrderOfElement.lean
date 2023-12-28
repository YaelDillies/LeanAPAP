import Mathlib.GroupTheory.OrderOfElement

/-!
### TODO

* Extra explicit argument to `zpow_mod_card`
* Extra implicit argument to `orderOf_dvd_natCard`
-/

variable {G : Type*} [Group G]

@[to_additive (attr := simp) mod_natCard_nsmul]
lemma pow_mod_natCard (a : G) (n : ℕ) : a ^ (n % Nat.card G) = a ^ n := by
  rw [eq_comm, ← pow_mod_orderOf, ← Nat.mod_mod_of_dvd n $ orderOf_dvd_natCard _, pow_mod_orderOf]

@[to_additive (attr := simp) mod_natCard_zsmul]
lemma zpow_mod_natCard (a : G) (n : ℤ) : a ^ (n % Nat.card G : ℤ) = a ^ n := by
  rw [eq_comm, ← zpow_mod_orderOf,
    ← Int.emod_emod_of_dvd n $ Int.coe_nat_dvd.2 $ orderOf_dvd_natCard _, zpow_mod_orderOf]
