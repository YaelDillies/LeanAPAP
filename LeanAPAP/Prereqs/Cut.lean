import Mathbin.Algebra.BigOperators.Order
import Mathbin.Data.Fin.Tuple.NatAntidiagonal
import Mathbin.Data.Finset.Pointwise
import Project.Mathlib.Algebra.BigOperators.Ring
import Project.Mathlib.Data.Finset.NatAntidiagonal

#align_import prereqs.cut

noncomputable section

variable {ι α : Type _} [DecidableEq ι]

-- yoinked from archive/100thms/partition
open Finset

open scoped BigOperators Pointwise

/--
Functions defined only on `s`, which sum to `n`. In other words, a partition of `n` indexed by `s`.
Every function in here is finitely supported, and the support is a subset of `s`.
This should be thought of as a generalisation of `finset.nat.antidiagonal_tuple` where
`antidiagonal_tuple k n` is the same thing as `cut (s : finset.univ (fin k)) n`.
-/
def cut (s : Finset ι) (n : ℕ) : Finset (ι → ℕ) :=
  Finset.filter (fun f => s.Sum f = n)
    ((s.pi fun _ => range (n + 1)).map
      ⟨fun f i => if h : i ∈ s then f i h else 0, fun f g h => by ext i hi;
        simpa [dif_pos hi] using congr_fun h i⟩)

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (i «expr ∉ » s) -/
theorem mem_cut (s : Finset ι) (n : ℕ) (f : ι → ℕ) :
    f ∈ cut s n ↔ s.Sum f = n ∧ ∀ (i) (_ : i ∉ s), f i = 0 :=
  by
  rw [cut, mem_filter, and_comm', and_congr_right]
  intro h
  simp only [mem_map, exists_prop, Function.Embedding.coeFn_mk, mem_pi]
  refine' ⟨_, fun hf => ⟨fun i hi => f i, fun i hi => _, _⟩⟩
  · rintro ⟨_, _, rfl⟩ _ _
    simp [dif_neg H]
  · rw [mem_range, Nat.lt_succ_iff, ← h]
    apply single_le_sum _ hi
    simp
  · ext
    rw [dite_eq_ite, ite_eq_left_iff, eq_comm]
    exact hf x

theorem cut_equiv_antidiag (n : ℕ) :
    Equiv.finsetCongr (Equiv.boolArrowEquivProd _) (cut univ n) = Nat.antidiagonal n :=
  by
  ext ⟨x₁, x₂⟩
  simp_rw [Equiv.finsetCongr_apply, mem_map, Equiv.toEmbedding, Function.Embedding.coeFn_mk, ←
    Equiv.eq_symm_apply]
  simp [mem_cut, add_comm]

theorem cut_univ_fin_eq_antidiagonalTuple (n k : ℕ) : cut univ n = Nat.antidiagonalTuple k n := by
  ext; simp [nat.mem_antidiagonal_tuple, mem_cut]

/-- There is only one `cut` of 0. -/
@[simp]
theorem cut_zero (s : Finset ι) : cut s 0 = {0} :=
  by
  -- In general it's nice to prove things using `mem_cut` but in this case it's easier to just
  -- use the definition.
  rw [cut, range_one, pi_const_singleton, map_singleton, Function.Embedding.coeFn_mk,
    filter_singleton, if_pos, singleton_inj]
  · ext; split_ifs <;> rfl
  rw [sum_eq_zero_iff]
  intro x hx
  apply dif_pos hx

@[simp]
theorem cut_empty_succ (n : ℕ) : cut (∅ : Finset ι) (n + 1) = ∅ :=
  eq_empty_of_forall_not_mem fun x hx => by simpa using hx

theorem cut_insert (n : ℕ) (a : ι) (s : Finset ι) (h : a ∉ s) : by
    classical exact
      cut (insert a s) n =
        (nat.antidiagonal n).biUnion fun p : ℕ × ℕ =>
          (cut s p.snd).map
            ⟨fun f => f + fun t => if t = a then p.fst else 0, add_left_injective _⟩ :=
  by
  ext f
  rw [mem_cut, mem_bUnion, sum_insert h]
  constructor
  · rintro ⟨rfl, h₁⟩
    simp only [exists_prop, Function.Embedding.coeFn_mk, mem_map, nat.mem_antidiagonal, Prod.exists]
    refine' ⟨f a, s.sum f, rfl, fun i => if i = a then 0 else f i, _, _⟩
    · rw [mem_cut]
      refine' ⟨_, _⟩
      · rw [sum_ite]
        have : Filter (fun x => x ≠ a) s = s :=
          by
          apply filter_true_of_mem
          rintro i hi rfl
          apply h hi
        simp [this]
      · intro i hi
        rw [ite_eq_left_iff]
        intro hne
        apply h₁
        simp [not_or, hne, hi]
    · ext
      obtain rfl | h := eq_or_ne x a
      · simp
      · simp [if_neg h]
  · simp only [mem_insert, Function.Embedding.coeFn_mk, mem_map, nat.mem_antidiagonal, Prod.exists,
      exists_prop, mem_cut, not_or]
    rintro ⟨p, q, rfl, g, ⟨rfl, hg₂⟩, rfl⟩
    refine' ⟨_, _⟩
    · simp [sum_add_distrib, if_neg h, hg₂ _ h, add_comm]
    · rintro i ⟨h₁, h₂⟩
      simp [if_neg h₁, hg₂ _ h₂]

theorem cut_insert_disjoint_bUnion (n : ℕ) (a : ι) (s : Finset ι) (h : a ∉ s) :
    (n.antidiagonal : Set (ℕ × ℕ)).PairwiseDisjoint fun p : ℕ × ℕ =>
      (cut s p.snd).map ⟨fun f => f + fun t => if t = a then p.fst else 0, add_left_injective _⟩ :=
  by
  simp only [Set.PairwiseDisjoint, Function.onFun_apply, Finset.disjoint_iff_ne, mem_map,
    Function.Embedding.coeFn_mk, Ne.def, forall_exists_index, Set.Pairwise, mem_coe, mem_cut,
    and_imp]
  rintro x hx y hy h' f g hg hg' rfl _ f hf hf' e rfl
  rw [nat.antidiagonal_congr' hx hy] at h' 
  simp only [Function.funext_iff, Pi.add_apply] at e 
  replace e := sum_congr rfl fun i (_ : i ∈ s) => e i
  rw [sum_add_distrib, hf, sum_ite_eq', if_neg h, sum_add_distrib, hg, sum_ite_eq', if_neg h,
    add_zero, add_zero] at e 
  exact h' e.symm

theorem nsmul_cut (s : Finset ι) (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    @SMul.smul _ _ Finset.smulFinset n (cut s m) =
      (cut s (n * m)).filterₓ fun f : ι → ℕ => ∀ i ∈ s, n ∣ f i :=
  by
  classical
  ext f
  simp only [mem_smul_finset, mem_filter, mem_cut, Function.Embedding.coeFn_mk, exists_prop,
    and_assoc']
  constructor
  · rintro ⟨f, rfl, hf, rfl⟩
    simpa [← mul_sum, hn] using hf
  rintro ⟨hfsum, hfsup, hfdvd⟩
  refine' ⟨fun i => f i / n, _⟩
  rw [← Nat.sum_div hfdvd, hfsum, Nat.mul_div_cancel_left _ hn.bot_lt]
  simp only [eq_self_iff_true, true_and_iff, Function.funext_iff]
  refine' ⟨fun i hi => _, fun i => _⟩
  · rw [hfsup _ hi, Nat.zero_div]
  dsimp
  by_cases i ∈ s
  · exact Nat.mul_div_cancel' (hfdvd _ h)
  · rw [hfsup _ h, Nat.zero_div, MulZeroClass.mul_zero]

theorem map_nsmul_cut (s : Finset ι) (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (cut s m).map
        ⟨(· • ·) n, fun f g h => funext fun i => mul_right_injective₀ hn (congr_fun h i)⟩ =
      (cut s (n * m)).filterₓ fun f : ι → ℕ => ∀ i ∈ s, n ∣ f i :=
  by rw [map_eq_image]; exact nsmul_cut _ _ hn

theorem nsmul_cut_univ [Fintype ι] (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    @SMul.smul _ _ Finset.smulFinset n (cut univ m) =
      (cut univ (n * m)).filterₓ fun f : ι → ℕ => ∀ i, n ∣ f i :=
  by
  have := nsmul_cut (univ : Finset ι) m hn
  simp at this 
  convert this

theorem map_nsmul_cut_univ [Fintype ι] (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (cut (univ : Finset ι) m).map
        ⟨(· • ·) n, fun f g h => funext fun i => mul_right_injective₀ hn (congr_fun h i)⟩ =
      (cut univ (n * m)).filterₓ fun f : ι → ℕ => ∀ i, n ∣ f i :=
  by simpa using map_nsmul_cut (univ : Finset ι) m hn

