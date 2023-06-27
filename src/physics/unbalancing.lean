import analysis.inner_product_space.pi_L2
import mathlib.algebra.big_operators.ring
import prereqs.lp_norm

/-!
# Unbalancing
-/

open finset real
open_locale big_operators complex_conjugate complex_order nnreal

variables {G : Type*} [fintype G] [decidable_eq G] [add_comm_group G] {ν : G → ℝ≥0} {f g h : G → ℂ}
  {p : ℝ≥0} {ε : ℝ}

/-- Note that we do the physical proof in order to avoid the Fourier transform. -/
lemma pow_inner_nonneg (hf : f = g ○ g) (hν : coe ∘ ν = h ○ h) (k : ℕ) :
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
  simp only [pow_sum, sum_mul_sum, map_mul, star_ring_end_self_apply, fintype.pi_finset_univ,
    ←inner_self_eq_norm_sq_to_K, sum_product, is_R_or_C.inner_apply, map_sum, map_prod,
     mul_mul_mul_comm, ←prod_mul_distrib],
  simp only [sum_mul, @sum_comm _ _ (fin k → G), mul_comm (conj _)],
  exact sum_comm,
end

/-- Note that we do the physical proof in order to avoid the Fourier transform. -/
lemma unbalancing' {p : ℕ} (hp' : odd p) (hp : 3 ≤ p) (hf : f = g ○ g) (hν : coe ∘ ν = h ○ h)
  (hε : ε ≤ ‖f‖_[p, ν]) :
  ∃ p' : ℕ, ↑p' ≤ 16 / ε * log (12 / ε) * p ∧ 1 + ε/2 ≤ ‖f + 1‖_[p', ν] :=
sorry

/-- The unbalancing step. Note that we do the physical proof in order to avoid the Fourier
transform. -/
lemma unbalancing (hp : 1 ≤ p) (hf : f = g ○ g) (hν : coe ∘ ν = h ○ h) (hε : ε ≤ ‖f‖_[p, ν]) :
  ∃ p' : ℝ≥0, ↑p' ≤ 16 / ε * log (48 / ε) * p ∧ 1 + ε/2 ≤ ‖f + 1‖_[p', ν] :=
sorry
