import topology.metric_space.algebra

variables {ι : Type*} [fintype ι]

instance pi.has_bounded_smul' {α : Type*} {β : ι → Type*} [pseudo_metric_space α]
  [Π i, pseudo_metric_space (β i)] [has_zero α] [Π i, has_zero (β i)] [Π i, has_smul α (β i)]
  [Π i, has_bounded_smul α (β i)] : has_bounded_smul α (Π i, β i) :=
{ dist_smul_pair' := sorry,
  dist_pair_smul' := sorry }

instance {α β : ι → Type*} [Π i, pseudo_metric_space (α i)] [Π i, pseudo_metric_space (β i)]
  [Π i,has_zero (α i)] [Π i, has_zero (β i)] [Π i, has_smul (α i) (β i)]
  [Π i, has_bounded_smul (α i) (β i)] : has_bounded_smul (Π i, α i) (Π i, β i) :=
{ dist_smul_pair' := sorry,
  dist_pair_smul' := sorry }
