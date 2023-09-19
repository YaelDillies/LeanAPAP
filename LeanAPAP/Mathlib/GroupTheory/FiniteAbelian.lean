import Mathlib.GroupTheory.FiniteAbelian
import LeanAPAP.Mathlib.Data.ZMod.Basic

open scoped DirectSum

private def myThingForward {ι : Type} [DecidableEq ι] (p : ι → ℕ) (n : ι → ℕ) :
    (⨁ i : {i // n i ≠ 0}, ZMod (p i ^ n i)) →+ ⨁ i, ZMod (p i ^ n i) :=
  DirectSum.toAddMonoid λ i ↦ DirectSum.of (λ i ↦ ZMod (p i ^ n i)) i

private def myThingBackward {ι : Type} [DecidableEq ι] (p : ι → ℕ) (n : ι → ℕ) :
    (⨁ i, ZMod (p i ^ n i)) →+ ⨁ i : {i // n i ≠ 0}, ZMod (p i ^ n i) :=
  DirectSum.toAddMonoid λ i ↦
    if h : n i = 0 then 0 else DirectSum.of (λ j : {i // n i ≠ 0} ↦ ZMod (p j ^ n j)) ⟨i, h⟩

private def myThing (ι : Type) [DecidableEq ι] (p : ι → ℕ) (n : ι → ℕ) :
    (⨁ i : {i // n i ≠ 0}, ZMod (p i ^ n i)) ≃+ ⨁ i, ZMod (p i ^ n i) where
  toFun := myThingForward p n
  invFun := myThingBackward p n
  left_inv x := by
    induction' x using DirectSum.induction_on with i x x y hx hy
    · simp
    · rw [myThingForward, DirectSum.toAddMonoid_of, myThingBackward, DirectSum.toAddMonoid_of,
        dif_neg i.prop]
    · rw [map_add, map_add, hx, hy]
  right_inv x := by
    induction' x using DirectSum.induction_on with i x x y hx hy
    · rw [map_zero, map_zero]
    · rw [myThingBackward, DirectSum.toAddMonoid_of]
      sorry
    --   split_ifs with h
    --   · simp [h, ZMod.subsingleton_of_eq_one x 0 (by rw [h, pow_zero])]
    --   · simp_rw [dif_neg h, myThingForward, DirectSum.toAddMonoid_of]
    · rw [map_add, map_add, hx, hy]
  map_add' := map_add (myThingForward p n)

/-- **Structure theorem of finite abelian groups** : Any finite abelian group is a direct sum of
some `ZMod (n i)` for some prime powers `n i > 1`. -/
lemma AddCommGroup.equiv_directSum_zmod_of_finite (G : Type*) [AddCommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ),
      (∀ i, 1 < n i) ∧ Nonempty (G ≃+ ⨁ i, ZMod (n i)) := by
  classical
  obtain ⟨ι, hι, p, hp, n, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_fintype G
  skip
  refine' ⟨{i : ι // n i ≠ 0}, inferInstance, λ i ↦ p i ^ n i, _, ⟨e.trans (myThing ι _ _).symm⟩⟩
  rintro ⟨i, hi⟩
  exact one_lt_pow (hp _).one_lt hi
