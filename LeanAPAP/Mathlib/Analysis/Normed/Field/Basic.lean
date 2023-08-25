import Mathbin.Analysis.Normed.Field.Basic
import Project.Mathlib.GroupTheory.OrderOfElement

#align_import mathlib.analysis.normed.field.basic

section

variable {α : Type _} [NormedDivisionRing α] {a : α}

protected theorem IsOfFinOrder.norm_eq_one (ha : IsOfFinOrder a) : ‖a‖ = 1 :=
  ((normHom : α →*₀ ℝ).toMonoidHom.IsOfFinOrder ha).eq_one <| norm_nonneg _

end

