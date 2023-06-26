import algebra.big_operators.order
import data.fin.tuple.nat_antidiagonal
import mathlib.data.finset.nat_antidiagonal

noncomputable theory

variables {ι α : Type*}

-- yoinked from archive/100thms/partition

open finset
open_locale big_operators classical

/--
Functions defined only on `s`, which sum to `n`. In other words, a partition of `n` indexed by `s`.
Every function in here is finitely supported, and the support is a subset of `s`.
This should be thought of as a generalisation of `finset.nat.antidiagonal_tuple` where
`antidiagonal_tuple k n` is the same thing as `cut (s : finset.univ (fin k)) n`.
-/
def cut (s : finset ι) (n : ℕ) : finset (ι → ℕ) :=
finset.filter (λ f, s.sum f = n) ((s.pi (λ _, range (n+1))).map
  ⟨λ f i, if h : i ∈ s then f i h else 0,
   λ f g h, by { ext i hi, simpa [dif_pos hi] using congr_fun h i }⟩)

lemma mem_cut (s : finset ι) (n : ℕ) (f : ι → ℕ) : f ∈ cut s n ↔ s.sum f = n ∧ ∀ i ∉ s, f i = 0 :=
begin
  rw [cut, mem_filter, and_comm, and_congr_right],
  intro h,
  simp only [mem_map, exists_prop, function.embedding.coe_fn_mk, mem_pi],
  split,
  { rintro ⟨_, _, rfl⟩ _ _,
    simp [dif_neg H] },
  { intro hf,
    refine ⟨λ i hi, f i, λ i hi, _, _⟩,
    { rw [mem_range, nat.lt_succ_iff, ← h],
      apply single_le_sum _ hi,
      simp },
    { ext,
      rw [dite_eq_ite, ite_eq_left_iff, eq_comm],
      exact hf x } }
end

lemma cut_equiv_antidiag (n : ℕ) :
  equiv.finset_congr (equiv.bool_arrow_equiv_prod _) (cut univ n) = nat.antidiagonal n :=
begin
  ext ⟨x₁, x₂⟩,
  simp_rw [equiv.finset_congr_apply, mem_map, equiv.to_embedding, function.embedding.coe_fn_mk,
           ←equiv.eq_symm_apply],
  simp [mem_cut, add_comm],
end

lemma cut_univ_fin_eq_antidiagonal_tuple (n k : ℕ) : cut univ n = nat.antidiagonal_tuple k n :=
by { ext, simp [nat.mem_antidiagonal_tuple, mem_cut] }

/-- There is only one `cut` of 0. -/
@[simp] lemma cut_zero (s : finset ι) : cut s 0 = {0} :=
begin
  -- In general it's nice to prove things using `mem_cut` but in this case it's easier to just
  -- use the definition.
  rw [cut, range_one, pi_const_singleton, map_singleton, function.embedding.coe_fn_mk,
      filter_singleton, if_pos, singleton_inj],
  { ext, split_ifs; refl },
  rw sum_eq_zero_iff,
  intros x hx,
  apply dif_pos hx,
end

@[simp] lemma cut_empty_succ (n : ℕ) : cut (∅ : finset ι) (n+1) = ∅ :=
eq_empty_of_forall_not_mem $ λ x hx, by simpa using hx

lemma cut_insert (n : ℕ) (a : ι) (s : finset ι) (h : a ∉ s) :
  cut (insert a s) n =
  (nat.antidiagonal n).bUnion
    (λ (p : ℕ × ℕ), (cut s p.snd).map
      ⟨λ f, f + λ t, if t = a then p.fst else 0, add_left_injective _⟩) :=
begin
  ext f,
  rw [mem_cut, mem_bUnion, sum_insert h],
  split,
  { rintro ⟨rfl, h₁⟩,
    simp only [exists_prop, function.embedding.coe_fn_mk, mem_map,
               nat.mem_antidiagonal, prod.exists],
    refine ⟨f a, s.sum f, rfl, λ i, if i = a then 0 else f i, _, _⟩,
    { rw [mem_cut],
      refine ⟨_, _⟩,
      { rw [sum_ite],
        have : (filter (λ x, x ≠ a) s) = s,
        { apply filter_true_of_mem,
          rintro i hi rfl,
          apply h hi },
        simp [this] },
      { intros i hi,
        rw ite_eq_left_iff,
        intro hne,
        apply h₁,
        simp [not_or_distrib, hne, hi] } },
    { ext,
      obtain rfl|h := eq_or_ne x a,
      { simp },
      { simp [if_neg h] } } },
  { simp only [mem_insert, function.embedding.coe_fn_mk, mem_map, nat.mem_antidiagonal, prod.exists,
               exists_prop, mem_cut, not_or_distrib],
    rintro ⟨p, q, rfl, g, ⟨rfl, hg₂⟩, rfl⟩,
    refine ⟨_, _⟩,
    { simp [sum_add_distrib, if_neg h, hg₂ _ h, add_comm] },
    { rintro i ⟨h₁, h₂⟩,
      simp [if_neg h₁, hg₂ _ h₂] } }
end

lemma cut_insert_disjoint_bUnion (n : ℕ) (a : ι) (s : finset ι) (h : a ∉ s) :
  (n.antidiagonal : set (ℕ × ℕ)).pairwise_disjoint (λ (p : ℕ × ℕ), (cut s p.snd).map
      ⟨λ f, f + λ t, if t = a then p.fst else 0, add_left_injective _⟩) :=
begin
  simp only [set.pairwise_disjoint, function.on_fun_apply, finset.disjoint_iff_ne, mem_map,
    function.embedding.coe_fn_mk, ne.def, forall_exists_index,
    set.pairwise, mem_coe, mem_cut, and_imp],
  rintro x hx y hy h' f g hg hg' rfl _ f hf hf' e rfl,
  rw nat.antidiagonal_congr' hx hy at h',
  simp only [function.funext_iff, pi.add_apply] at e,
  replace e := sum_congr rfl (λ i (_ : i ∈ s), e i),
  rw [sum_add_distrib, hf, sum_ite_eq', if_neg h, sum_add_distrib, hg, sum_ite_eq', if_neg h,
    add_zero, add_zero] at e,
  exact h' e.symm
end
