import Mathlib.Analysis.Normed.Field.Basic
import LeanAPAP.Mathlib.GroupTheory.OrderOfElement

#align_import mathlib.analysis.normed.field.basic

section

variable {α : Type*} [NormedDivisionRing α] {a : α}

protected lemma IsOfFinOrder.norm_eq_one (ha : IsOfFinOrder a) : ‖a‖ = 1 :=
  ((normHom : α →*₀ ℝ).toMonoidHom.IsOfFinOrder ha).eq_one <| norm_nonneg _

end
