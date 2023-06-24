import analysis.normed_space.ray
import mathlib.linear_algebra.ray

section normed_add_comm_group
variables {E : Type*} [normed_add_comm_group E]

lemma norm_nsmul [normed_space ℝ E] (n : ℕ) (x : E) : ‖n • x‖ = n • ‖x‖ :=
begin
  induction n with n ih,
  { simp },
  { rw [succ_nsmul, succ_nsmul, same_ray.norm_add, ih],
    exact same_ray_nsmul_right _ _ }
end

end normed_add_comm_group
