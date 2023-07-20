import group_theory.finite_abelian
import mathlib.data.zmod.basic

open_locale direct_sum

private def my_thing_forward {ι : Type} [decidable_eq ι] (p : ι → ℕ) (n : ι → ℕ) :
  (⨁ (i : {i // n i ≠ 0}), zmod (p i ^ n i)) →+ ⨁ i, zmod (p i ^ n i) :=
direct_sum.to_add_monoid $ λ i, direct_sum.of (λ i, zmod (p i ^ n i)) i

private def my_thing_backward {ι : Type} [decidable_eq ι] (p : ι → ℕ) (n : ι → ℕ) :
  (⨁ i, zmod (p i ^ n i)) →+ ⨁ (i : {i // n i ≠ 0}), zmod (p i ^ n i) :=
direct_sum.to_add_monoid $ λ i,
  if h : n i = 0 then 0 else direct_sum.of (λ (j : {i // n i ≠ 0}), zmod (p j ^ n j)) ⟨i, h⟩

private def my_thing (ι : Type) [decidable_eq ι] (p : ι → ℕ) (n : ι → ℕ) :
  (⨁ (i : {i // n i ≠ 0}), zmod (p i ^ n i)) ≃+ ⨁ i, zmod (p i ^ n i) :=
{ to_fun := my_thing_forward p n,
  inv_fun := my_thing_backward p n,
  left_inv := λ x, begin
    induction x using direct_sum.induction_on with i x x y hx hy,
    { simp },
    { rw [my_thing_forward, direct_sum.to_add_monoid_of, my_thing_backward,
        direct_sum.to_add_monoid_of, dif_neg i.prop],
      cases i,
      refl },
    { rw [map_add, map_add, hx, hy] }
  end,
  right_inv := λ x, begin
    induction x using direct_sum.induction_on with i x x y hx hy,
    { simp },
    { rw [my_thing_backward, direct_sum.to_add_monoid_of],
      split_ifs,
      { rw [add_monoid_hom.zero_apply, map_zero,
          (zmod.subsingleton_of_eq_one x 0 (by rw [h, pow_zero])), map_zero] },
      { rw [my_thing_forward, direct_sum.to_add_monoid_of],
        refl } },
    { rw [map_add, map_add, hx, hy] }
  end,
  map_add' := λ x y, by rw map_add }

/-- **Structure theorem of finite abelian groups** : Any finite abelian group is a direct sum of
some `zmod (n i)` for some prime powers `n i > 1`. -/
theorem add_comm_group.equiv_direct_sum_zmod_of_finite (G : Type*) [add_comm_group G] [finite G] :
  ∃ (ι : Type) [fintype ι] (n : ι → ℕ) (hn : ∀ i, 1 < n i),
  nonempty $ G ≃+ direct_sum ι (λ (i : ι), zmod (n i)) :=
begin
  classical,
  obtain ⟨ι, hι, p, hp, n, ⟨e⟩⟩ := add_comm_group.equiv_direct_sum_zmod_of_fintype G,
  resetI,
  refine ⟨{i : ι // n i ≠ 0}, infer_instance, λ i, p i ^ n i, _, ⟨e.trans (my_thing _ _ _).symm⟩⟩,
  rintro ⟨i, hi⟩,
  exact one_lt_pow (hp _).one_lt hi,
end
