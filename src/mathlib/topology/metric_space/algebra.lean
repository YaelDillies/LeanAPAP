import topology.metric_space.algebra

variables {ι : Type*} [fintype ι]

instance pi.has_bounded_smul' {α : Type*} {β : ι → Type*} [pseudo_metric_space α]
  [Π i, pseudo_metric_space (β i)] [has_zero α] [Π i, has_zero (β i)] [Π i, has_smul α (β i)]
  [Π i, has_bounded_smul α (β i)] : has_bounded_smul α (Π i, β i) :=
{ dist_smul_pair' := λ x y₁ y₂, (dist_pi_le_iff $ by positivity).2 $ λ i,
    (dist_smul_pair _ _ _).trans $ mul_le_mul_of_nonneg_left (dist_le_pi_dist _ _ _) dist_nonneg,
  dist_pair_smul' := λ x₁ x₂ y, (dist_pi_le_iff $ by positivity).2 $ λ i,
    (dist_pair_smul _ _ _).trans $ mul_le_mul_of_nonneg_left (dist_le_pi_dist _ _ _) dist_nonneg }

instance {α β : ι → Type*} [Π i, pseudo_metric_space (α i)] [Π i, pseudo_metric_space (β i)]
  [Π i, has_zero (α i)] [Π i, has_zero (β i)] [Π i, has_smul (α i) (β i)]
  [Π i, has_bounded_smul (α i) (β i)] : has_bounded_smul (Π i, α i) (Π i, β i) :=
{ dist_smul_pair' := λ x y₁ y₂, (dist_pi_le_iff $ by positivity).2 $ λ i,
    (dist_smul_pair _ _ _).trans $ mul_le_mul (dist_le_pi_dist _ _ _) (dist_le_pi_dist _ _ _)
    dist_nonneg dist_nonneg,
  dist_pair_smul' := λ x₁ x₂ y, (dist_pi_le_iff $ by positivity).2 $ λ i,
    (dist_pair_smul _ _ _).trans $ mul_le_mul (dist_le_pi_dist _ _ _) (dist_le_pi_dist _ _ _)
    dist_nonneg dist_nonneg }

instance prod.has_bounded_smul' {α β γ : Type*} [pseudo_metric_space α] [pseudo_metric_space β]
  [pseudo_metric_space γ] [has_zero α] [has_zero β] [has_zero γ] [has_smul α β] [has_smul α γ]
  [has_bounded_smul α β] [has_bounded_smul α γ] : has_bounded_smul α (β × γ) :=
{ dist_smul_pair' := λ x y₁ y₂, max_le
    ((dist_smul_pair _ _ _).trans $ mul_le_mul_of_nonneg_left (le_max_left _ _) dist_nonneg)
    ((dist_smul_pair _ _ _).trans $ mul_le_mul_of_nonneg_left (le_max_right _ _) dist_nonneg),
  dist_pair_smul' := λ x₁ x₂ y, max_le
    ((dist_pair_smul _ _ _).trans $ mul_le_mul_of_nonneg_left (le_max_left _ _) dist_nonneg)
    ((dist_pair_smul _ _ _).trans $ mul_le_mul_of_nonneg_left (le_max_right _ _) dist_nonneg) }

-- We don't have the `has_smul α γ → has_smul β δ → has_smul (α × β) (γ × δ)` instance, but if we
-- did, then `has_bounded_smul α γ → has_bounded_smul β δ → has_bounded_smul (α × β) (γ × δ)` would
-- hold
