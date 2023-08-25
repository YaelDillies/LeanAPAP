import Mathbin.Topology.MetricSpace.Algebra

#align_import mathlib.topology.metric_space.algebra

variable {ι : Type _} [Fintype ι]

instance Pi.has_bounded_smul' {α : Type _} {β : ι → Type _} [PseudoMetricSpace α]
    [∀ i, PseudoMetricSpace (β i)] [Zero α] [∀ i, Zero (β i)] [∀ i, SMul α (β i)]
    [∀ i, BoundedSMul α (β i)] : BoundedSMul α (∀ i, β i)
    where
  dist_smul_pair' x y₁ y₂ :=
    (dist_pi_le_iff <| by positivity).2 fun i =>
      (dist_smul_pair _ _ _).trans <| mul_le_mul_of_nonneg_left (dist_le_pi_dist _ _ _) dist_nonneg
  dist_pair_smul' x₁ x₂ y :=
    (dist_pi_le_iff <| by positivity).2 fun i =>
      (dist_pair_smul _ _ _).trans <| mul_le_mul_of_nonneg_left (dist_le_pi_dist _ _ _) dist_nonneg

instance {α β : ι → Type _} [∀ i, PseudoMetricSpace (α i)] [∀ i, PseudoMetricSpace (β i)]
    [∀ i, Zero (α i)] [∀ i, Zero (β i)] [∀ i, SMul (α i) (β i)] [∀ i, BoundedSMul (α i) (β i)] :
    BoundedSMul (∀ i, α i) (∀ i, β i)
    where
  dist_smul_pair' x y₁ y₂ :=
    (dist_pi_le_iff <| by positivity).2 fun i =>
      (dist_smul_pair _ _ _).trans <|
        mul_le_mul (dist_le_pi_dist _ _ _) (dist_le_pi_dist _ _ _) dist_nonneg dist_nonneg
  dist_pair_smul' x₁ x₂ y :=
    (dist_pi_le_iff <| by positivity).2 fun i =>
      (dist_pair_smul _ _ _).trans <|
        mul_le_mul (dist_le_pi_dist _ _ _) (dist_le_pi_dist _ _ _) dist_nonneg dist_nonneg

instance Prod.has_bounded_smul' {α β γ : Type _} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [PseudoMetricSpace γ] [Zero α] [Zero β] [Zero γ] [SMul α β] [SMul α γ] [BoundedSMul α β]
    [BoundedSMul α γ] : BoundedSMul α (β × γ)
    where
  dist_smul_pair' x y₁ y₂ :=
    max_le ((dist_smul_pair _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_left _ _) dist_nonneg)
      ((dist_smul_pair _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_right _ _) dist_nonneg)
  dist_pair_smul' x₁ x₂ y :=
    max_le ((dist_pair_smul _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_left _ _) dist_nonneg)
      ((dist_pair_smul _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_right _ _) dist_nonneg)

-- We don't have the `has_smul α γ → has_smul β δ → has_smul (α × β) (γ × δ)` instance, but if we
-- did, then `has_bounded_smul α γ → has_bounded_smul β δ → has_bounded_smul (α × β) (γ × δ)` would
-- hold
