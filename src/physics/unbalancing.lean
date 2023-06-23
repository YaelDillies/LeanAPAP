import analysis.inner_product_space.pi_L2
import mathlib.algebra.big_operators.ring
import mathlib.convolution
import misc

/-!
# Unbalancing
-/

open finset
open_locale big_operators complex_order complex_conjugate nnreal

variables {G : Type*} [fintype G] [decidable_eq G] [add_comm_group G] {ν : G → ℝ≥0} {f g h : G → ℂ}
  {p : ℝ≥0} {ε : ℝ}

/-- Note that we do the physical proof in order to avoid the Fourier transform. -/
lemma inner_pow (hf : f = g ○ g) (hν : coe ∘ ν = h ○ h) (k : ℕ) :
  (0 : ℂ) ≤ ⟪f ^ k, (coe : ℝ≥0 → ℂ) ∘ ν⟫_[ℂ] :=
begin
  rw [hf, hν, L2inner_eq_sum],
  simp only [pi_Lp.equiv_symm_apply, pi.pow_apply, is_R_or_C.inner_apply, map_pow],
  simp_rw [dconv_def, map_sum, pow_sum, sum_mul_sum],
  simp only [univ_product_univ, map_mul, star_ring_end_self_apply, fintype.pi_finset_univ],
  sorry, -- must shift the `h` part of the sum
  -- refine sum_nonneg (λ y _, sum_nonneg $ λ gh _, mul_nonneg _ $ star_mul_self_nonneg' _),
  -- sorry
end

/-- The unbalancing step. Note that we do the physical proof in order to avoid the Fourier
transform. -/
lemma unbalancing (hp : 1 ≤ p) (hf : f = g ○ g) (hν : coe ∘ ν = h ○ h) (hε : ε ≤ ‖g ○ g‖_[p, ν]) :
  ∃ p', 1 + ε/2 ≤ ‖f + 1‖_[p', ν] :=
sorry
