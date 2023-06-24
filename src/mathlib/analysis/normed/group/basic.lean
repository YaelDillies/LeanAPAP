import analysis.normed.group.basic

section normed_add_comm_group
variables {α : Type*} [normed_add_comm_group α] {a b c : α}

lemma norm_sub_le_norm_sub_add_norm_sub : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ :=
(norm_add_le _ _).trans_eq' $ by simp

end normed_add_comm_group
