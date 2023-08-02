import mathlib.number_theory.legendre_symbol.add_char.basic
import prereqs.convolution.order
import prereqs.dissociation

noncomputable theory

open finset fintype
open_locale big_operators nat

variables {G : Type*} [add_comm_group G] [fintype G] {A : finset G}

def energy (n : ℕ) (A : finset G) (ν : G → ℂ) : ℝ :=
∑ γ in fintype.pi_finset (λ _ : fin n, A), ∑ δ in fintype.pi_finset (λ _ : fin n, A),
  ‖ν (∑ i, γ i - ∑ i, δ i)‖

lemma energy_nsmul (m n : ℕ) (A : finset G) (ν : G → ℂ) : energy n A (m • ν) = m • energy n A ν :=
by simp only [energy, nsmul_eq_mul, mul_sum, @pi.coe_nat G (λ _, ℂ) _ m, pi.mul_apply, norm_mul,
  complex.norm_nat]

variables [decidable_eq G]

def boring_energy (n : ℕ) (A : finset G) : ℝ := energy n A triv_char

lemma boring_energy_eq (n : ℕ) (A : finset G) : boring_energy n A = ∑ x, (𝟭 A ∗^ n) x ^ 2 :=
begin
  classical,
  simp only [boring_energy, energy, apply_ite norm, triv_char_apply, norm_one, norm_zero,
    sum_boole, sub_eq_zero],
  rw ←finset.sum_fiberwise _ (λ f : fin n → G, ∑ i, f i),
  congr' with x,
  rw [indicate_iter_conv_apply, sq, ←nsmul_eq_mul, ←sum_const],
  refine sum_congr rfl (λ f hf, _),
  simp_rw [(mem_filter.1 hf).2, eq_comm],
end

--TODO(Thomas): Figure out the constant
def thomas_const : ℕ := sorry

lemma finset.add_dissociated.indicate_iter_conv_apply_le (hA : A.add_dissociated) :
  ∀ (n : ℕ) (a : G), (𝟭_[ℝ] A ∗^ n) a ≤ thomas_const ^ n * n ^ n := sorry

lemma finset.add_dissociated.boring_energy_le (hA : A.add_dissociated) (n : ℕ) :
  boring_energy n A ≤ thomas_const ^ n * n ^ n * A.card ^ n :=
calc
    boring_energy n A
      = ∑ x, (𝟭 A ∗^ n) x * (𝟭 A ∗^ n) x : by simp_rw [boring_energy_eq, sq]
  ... ≤ ∑ x, thomas_const ^ n * n ^ n * (𝟭 A ∗^ n) x
      : sum_le_sum $ λ x _, mul_le_mul_of_nonneg_right
        (hA.indicate_iter_conv_apply_le _ _) $ iter_conv_nonneg indicate_nonneg _
  ... = _ : by rw [←mul_sum, sum_iter_conv, sum_indicate]
