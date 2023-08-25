import Mathbin.GroupTheory.FiniteAbelian
import Project.Mathlib.Data.Zmod.Basic

#align_import mathlib.group_theory.finite_abelian

open scoped DirectSum

private def my_thing_forward {ι : Type} [DecidableEq ι] (p : ι → ℕ) (n : ι → ℕ) :
    (⨁ i : { i // n i ≠ 0 }, ZMod (p i ^ n i)) →+ ⨁ i, ZMod (p i ^ n i) :=
  DirectSum.toAddMonoid fun i => DirectSum.of (fun i => ZMod (p i ^ n i)) i

private def my_thing_backward {ι : Type} [DecidableEq ι] (p : ι → ℕ) (n : ι → ℕ) :
    (⨁ i, ZMod (p i ^ n i)) →+ ⨁ i : { i // n i ≠ 0 }, ZMod (p i ^ n i) :=
  DirectSum.toAddMonoid fun i =>
    if h : n i = 0 then 0 else DirectSum.of (fun j : { i // n i ≠ 0 } => ZMod (p j ^ n j)) ⟨i, h⟩

private def my_thing (ι : Type) [DecidableEq ι] (p : ι → ℕ) (n : ι → ℕ) :
    (⨁ i : { i // n i ≠ 0 }, ZMod (p i ^ n i)) ≃+ ⨁ i, ZMod (p i ^ n i)
    where
  toFun := myThingForward p n
  invFun := myThingBackward p n
  left_inv x := by
    induction' x using DirectSum.induction_on with i x x y hx hy
    · simp
    · rw [my_thing_forward, DirectSum.toAddMonoid_of, my_thing_backward, DirectSum.toAddMonoid_of,
        dif_neg i.prop]
      cases i
      rfl
    · rw [map_add, map_add, hx, hy]
  right_inv x := by
    induction' x using DirectSum.induction_on with i x x y hx hy
    · simp
    · rw [my_thing_backward, DirectSum.toAddMonoid_of]
      split_ifs
      ·
        rw [AddMonoidHom.zero_apply, map_zero,
          ZMod.subsingleton_of_eq_one x 0 (by rw [h, pow_zero]), map_zero]
      · rw [my_thing_forward, DirectSum.toAddMonoid_of]
        rfl
    · rw [map_add, map_add, hx, hy]
  map_add' x y := by rw [map_add]

/-- **Structure theorem of finite abelian groups** : Any finite abelian group is a direct sum of
some `zmod (n i)` for some prime powers `n i > 1`. -/
theorem AddCommGroup.equiv_directSum_zMod_of_finite (G : Type _) [AddCommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ) (hn : ∀ i, 1 < n i),
      Nonempty <| G ≃+ DirectSum ι fun i : ι => ZMod (n i) :=
  by
  classical
  obtain ⟨ι, hι, p, hp, n, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_fintype G
  skip
  refine'
    ⟨{ i : ι // n i ≠ 0 }, inferInstance, fun i => p i ^ n i, _, ⟨e.trans (my_thing _ _ _).symm⟩⟩
  rintro ⟨i, hi⟩
  exact one_lt_pow (hp _).one_lt hi

