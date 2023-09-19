import Mathlib.Topology.MetricSpace.Algebra

variable {ι : Type*} [Fintype ι]

instance Pi.instBoundedSMul' {α : Type*} {β : ι → Type*} [PseudoMetricSpace α]
    [∀ i, PseudoMetricSpace (β i)] [Zero α] [∀ i, Zero (β i)] [∀ i, SMul α (β i)]
    [∀ i, BoundedSMul α (β i)] : BoundedSMul α (∀ i, β i)
    where
  dist_smul_pair' x y₁ y₂ :=
    (dist_pi_le_iff $ by positivity).2 λ i ↦
      (dist_smul_pair _ _ _).trans $ mul_le_mul_of_nonneg_left (dist_le_pi_dist _ _ _) dist_nonneg
  dist_pair_smul' x₁ x₂ y :=
    (dist_pi_le_iff $ by positivity).2 λ i ↦
      (dist_pair_smul _ _ _).trans $ mul_le_mul_of_nonneg_left (dist_le_pi_dist _ 0 _) dist_nonneg

instance Pi.instBoundedSMul {α β : ι → Type*} [∀ i, PseudoMetricSpace (α i)]
    [∀ i, PseudoMetricSpace (β i)] [∀ i, Zero (α i)] [∀ i, Zero (β i)] [∀ i, SMul (α i) (β i)]
    [∀ i, BoundedSMul (α i) (β i)] : BoundedSMul (∀ i, α i) (∀ i, β i) where
  dist_smul_pair' x y₁ y₂ :=
    (dist_pi_le_iff $ by positivity).2 λ i ↦
      (dist_smul_pair _ _ _).trans $
        mul_le_mul (dist_le_pi_dist _ 0 _) (dist_le_pi_dist _ _ _) dist_nonneg dist_nonneg
  dist_pair_smul' x₁ x₂ y :=
    (dist_pi_le_iff $ by positivity).2 λ i ↦
      (dist_pair_smul _ _ _).trans $
        mul_le_mul (dist_le_pi_dist _ _ _) (dist_le_pi_dist _ 0 _) dist_nonneg dist_nonneg

instance Prod.has_bounded_smul' {α β γ : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [PseudoMetricSpace γ] [Zero α] [Zero β] [Zero γ] [SMul α β] [SMul α γ] [BoundedSMul α β]
    [BoundedSMul α γ] : BoundedSMul α (β × γ)
    where
  dist_smul_pair' _x _y₁ _y₂ :=
    max_le ((dist_smul_pair _ _ _).trans $ mul_le_mul_of_nonneg_left (le_max_left _ _) dist_nonneg)
      ((dist_smul_pair _ _ _).trans $ mul_le_mul_of_nonneg_left (le_max_right _ _) dist_nonneg)
  dist_pair_smul' _x₁ _x₂ _y :=
    max_le ((dist_pair_smul _ _ _).trans $ mul_le_mul_of_nonneg_left (le_max_left _ _) dist_nonneg)
      ((dist_pair_smul _ _ _).trans $ mul_le_mul_of_nonneg_left (le_max_right _ _) dist_nonneg)

-- We don't have the `SMul α γ → SMul β δ → SMul (α × β) (γ × δ)` instance, but if we
-- did, then `BoundedSMul α γ → BoundedSMul β δ → BoundedSMul (α × β) (γ × δ)` would
-- hold
