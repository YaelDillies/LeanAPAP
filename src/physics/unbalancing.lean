import analysis.inner_product_space.pi_L2
import mathlib.algebra.big_operators.ring
import mathlib.algebra.order.lattice_group
import mathlib.data.nat.order.basic
import prereqs.convolution
import prereqs.lp_norm

/-!
# Unbalancing
-/

open finset real
open_locale big_operators complex_conjugate complex_order nnreal

variables {G : Type*} [fintype G] [decidable_eq G] [add_comm_group G] {ν : G → ℝ≥0} {f : G → ℝ}
  {g h : G → ℂ} {p : ℝ≥0} {ε : ℝ}

/-- Note that we do the physical proof in order to avoid the Fourier transform. -/
lemma pow_inner_nonneg' {f : G → ℂ} (hf : f = g ○ g) (hν : coe ∘ ν = h ○ h) (k : ℕ) :
  (0 : ℂ) ≤ ⟪f ^ k, coe ∘ ν⟫_[ℂ] :=
begin
  suffices : ⟪f ^ k, coe ∘ ν⟫_[ℂ] = ∑ z : fin k → G, ‖∑ x, (∏ i, conj (g (x + z i))) * h x‖ ^ 2,
  { rw this,
    exact sum_nonneg (λ z _, by simp) },
  rw [hf, hν, L2inner_eq_sum],
  simp only [pi_Lp.equiv_symm_apply, pi.pow_apply, is_R_or_C.inner_apply, map_pow],
  simp_rw [dconv_apply h, mul_sum],
  --TODO: Please make `conv` work here :(
  have : ∀ x, ∀ yz ∈ univ.filter (λ yz : G × G, yz.1 - yz.2 = x),
    conj ((g ○ g) x) ^ k * (h yz.1 * conj (h yz.2)) =
      conj ((g ○ g) (yz.1 - yz.2)) ^ k * (h yz.1 * conj (h yz.2)),
  { simp only [mem_filter, mem_univ, true_and],
    rintro _ _ rfl,
    refl },
  simp_rw [sum_congr rfl (this _), dconv_apply_sub, sum_fiberwise, ←univ_product_univ, sum_product],
  simp only [sum_pow', sum_mul_sum, map_mul, star_ring_end_self_apply, fintype.pi_finset_univ,
    ←inner_self_eq_norm_sq_to_K, sum_product, is_R_or_C.inner_apply, map_sum, map_prod,
     mul_mul_mul_comm, ←prod_mul_distrib],
  simp only [sum_mul, @sum_comm _ _ (fin k → G), mul_comm (conj _)],
  exact sum_comm,
end

/-- Note that we do the physical proof in order to avoid the Fourier transform. -/
lemma pow_inner_nonneg {f : G → ℝ} (hf : coe ∘ f = g ○ g) (hν : coe ∘ ν = h ○ h) (k : ℕ) :
  0 ≤ ⟪(coe ∘ ν : G → ℝ), f ^ k⟫_[ℝ] :=
begin
  sorry
end

/-- Note that we do the physical proof in order to avoid the Fourier transform. -/
lemma unbalancing' {p : ℕ} (hp' : odd p) (hp : 5 ≤ p) (hν₁ : ‖(coe ∘ ν : G → ℝ)‖_[1] = 1)
  (hν : coe ∘ ν = h ○ h) (hf : coe ∘ f = g ○ g) (hε₀ : 0 < ε) (hε : ε ≤ ‖f‖_[p, ν]) :
  ∃ p' : ℕ, ↑p' ≤ 16 / ε * log (12 / ε) * p ∧ 1 + ε/2 ≤ ‖f + 1‖_[p', ν] :=
begin
  have : ε ^ p ≤ 2 * ∑ i, ↑(ν i) * ((f ^ (p - 1)) i * f⁺ i),
  sorry { calc
      ε ^ p ≤ ‖f‖_[p, ν] ^ p : hp'.strict_mono_pow.monotone hε
      ... = ∑ i, ν i • ((f ^ (p - 1)) i * |f| i) : _
      ... ≤ ⟪(coe ∘ ν : G → ℝ), f ^ p⟫_[ℝ] + ∑ i, ↑(ν i) * ((f ^ (p - 1)) i * |f| i)
          : le_add_of_nonneg_left $ pow_inner_nonneg hf hν _
      ... = _ : _,
    rw wLpnorm_pow_eq_sum hp'.pos.ne',
    dsimp,
    refine sum_congr rfl (λ i _, _),
    rw [←abs_of_nonneg ((nat.odd.sub_odd hp' odd_one).pow_nonneg $ f _), abs_pow,
      pow_sub_one_mul hp'.pos.ne'],
    simp [L2inner_eq_sum, ←sum_add_distrib, ←mul_add, ←pow_sub_one_mul hp'.pos.ne' (f _), mul_sum,
      mul_left_comm (2 : ℝ), add_abs_eq_two_nsmul_pos_part] },
  set P := univ.filter (λ i, 0 ≤ f i) with hP,
  set T := univ.filter (λ i, 3/4 * ε ≤ f i) with hT,
  have hTP : T ⊆ P := monotone_filter_right _  (λ i, le_trans $ by positivity),
  have : 2⁻¹ * ε ^ p ≤ ∑ i in P,↑(ν i) * (f ^ p) i,
  sorry { rw [inv_mul_le_iff (zero_lt_two' ℝ), sum_filter],
    convert this,
    ext i,
    rw [pi.pos_part_apply, pos_part_eq_ite],
    split_ifs; simp [pow_sub_one_mul hp'.pos.ne'] },
  have : ∑ i in P \ T, ↑(ν i) * (f ^ p) i ≤ 4⁻¹ * ε ^ p,
  sorry { calc
        _ ≤ ∑ i in P \ T, ↑(ν i) * (3/4 * ε) ^ p : sum_le_sum $ λ i hi, _
      ... = (3/4) ^ p * ε ^ p * ∑ i in P \ T, ν i : by rw [←sum_mul, mul_comm, mul_pow]
      ... ≤ 4⁻¹ * ε ^ p * ∑ i, ν i : _
      ... = 4⁻¹ * ε ^ p : _,
    { simp only [mem_sdiff, mem_filter, mem_univ, true_and, not_le] at hi,
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left hi.1 hi.2.le _) (by positivity) },
    { refine mul_le_mul (mul_le_mul_of_nonneg_right (le_trans (pow_le_pow_of_le_one _ _ hp) _) $ _)
        (sum_le_univ_sum_of_nonneg $ λ i, _) (sum_nonneg $ λ i _, _) _; positivity <|> norm_num },
    { simp only [L1norm_eq_sum, nnreal.norm_eq] at hν₁,
      rw [hν₁, mul_one] } },
  sorry
end

/-- The unbalancing step. Note that we do the physical proof in order to avoid the Fourier
transform. -/
lemma unbalancing (hp : 1 ≤ p) (hf : coe ∘ f = g ○ g) (hν : coe ∘ ν = h ○ h) (hε : ε ≤ ‖f‖_[p, ν]) :
  ∃ p' : ℝ≥0, ↑p' ≤ 16 / ε * log (48 / ε) * p ∧ 1 + ε/2 ≤ ‖f + 1‖_[p', ν] :=
sorry
